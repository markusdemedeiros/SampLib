import SampLib.Discrete.WeightedChoice
import SampLib.Discrete.Laws.NegativeMultinomial
import SampLib.Common.Laws.WeightedSupport
import SampLib.Discrete.Support.NatCounters
import SampLib.Core.SupportedSpec
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Compound
import Metrology.Iris.LocalBI

/-! # Negative-multinomial category counts

The success category lowers the remaining target; a failure increments its own
counter. The canonical negative-binomial/multinomial mixture supplies the
categorical recurrence. Its remaining-target potential funds one fixed
amplification independently of the accumulated failure counts.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.NegativeMultinomial

noncomputable section

private def validate {rT : Type _} : Exp rT := pl%
  rec check weights := case! weights
    | inl(u) => #true
    | inr(p) => if fst(p) < #0 then #false else check (snd(p))

private instance weighted_closed {rT : Type _} : ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Exp.fv, UniformInt.uniformInt_fv]

private instance increment_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.incrementCounter : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.incrementCounter, Exp.fv]

private instance zero_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.zeroCounters : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.zeroCounters, Exp.fv]

private instance length_closed {rT : Type _} : ClosedExp (Occil.length : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.length, Exp.fv]

-- Insert the static weights after constructing binders, so encoded data cannot be captured.
private def loop {rT : Type _} [ProbLangℝ rT] (s : ℕ) (ws : List ℕ) : Exp rT :=
  .fix (.lam (.lam pl(
    if {Exp.bvar 1} = #0 then {Exp.bvar 0} else
      {Exp.app (.lam pl(
        if {Exp.bvar 0} = #0 then
          {Exp.bvar 3} ({Exp.bvar 2} - #1) {Exp.bvar 1}
        else {Exp.bvar 3} {Exp.bvar 2}
          (&Occil.DiscreteExtra.incrementCounter {Exp.bvar 1} ({Exp.bvar 0} - #1))))
        pl(&Occil.weightedChoice &(NatCounters.encode (s :: ws)).fst)})))

private theorem zero_test {rT : Type _} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = decide (n = 0) := by
  change decide ((n : ℤ) = 0) = decide (n = 0)
  exact decide_eq_decide.mpr (by omega)

private theorem pred_cast (n : ℕ) (hn : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private theorem guard_test (s : ℕ) (hs : 0 < s) :
    Bool.or false (decide ((s : ℤ) ≤ 0)) = false := by simp [Nat.ne_of_gt hs]

private theorem termination_credit (ε : ℝ≥0∞) (hε : 0 < ε) (r : ℕ) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ε = r * δ + δ := by
  refine ⟨ε / (r + 1), ENNReal.div_pos hε.ne' (by finiteness), ?_⟩
  have h : ε / (r + 1) * (r + 1) = ε :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one, mul_comm (ε / (r + 1))] at h
  exact h.symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_validate (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&validate &(NatCounters.encode ws).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [NatCounters.encode, listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [NatCounters.encode, listVal]
    iterate 8 twp_pure
    exact IH

private theorem twp_loop_amplification (E : CoPset) (s : ℕ) (ws : List ℕ) (hs : 0 < s)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ r : ℕ, ∀ acc : List ℕ, ⌜acc.length = ws.length⌝ -∗
      ∀ F : List ℕ → ℝ≥0∞, ↯ (credit r s ws acc F + r * δ) -∗
        tglWp E pl(&(loop s ws) #int (r : ℤ) &(NatCounters.encode acc).fst)
          (fun v : Val rT => iprop(∃ cs : List ℕ,
            ⌜v = NatCounters.encode cs⌝ ∗ ↯ (F cs))) := by
  let _ : NeZero (s :: ws).sum := ⟨by simp only [List.sum_cons]; omega⟩
  iintro Hterm
  iapply ErrorCredit.Induction.simple hδ (one_lt_factor s ws hs) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %r %acc %hlen %F Hcredit
  iterate 4 twp_pure
  simp only [ClosedExp.openRec]
  rw [zero_test r]
  by_cases hr0 : r = 0
  · subst r
    rw [decide_eq_true rfl]
    twp_pure
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    isimp only [credit_zero s ws acc hlen F] at Hcredit
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (NatCounters.encode acc)))
    iexists acc
    iframe Hcredit
    itrivial
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    rw [decide_eq_false hr0]
    twp_pure
    twp_bind pl(&Occil.weightedChoice &(NatCounters.encode (s :: ws)).fst)
    icombine Hcredit Hterm as Hcredit
    isimp only [← conservation r s ws acc hr hs F δ] at Hcredit
    iapply ((WeightedChoice.weightedChoice_distSpec E (s :: ws)).wp_supported
      (fun i => i < (s :: ws).length) ((Set.to_countable _).measurableSet)
      (WeightedChoice.ae_lt_length (s :: ws)) (stepCredit r s ws acc F δ)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %category %hcategory Hcredit
    iterate 2 twp_pure
    rw [zero_test category]
    cases category with
    | zero =>
      rw [decide_eq_true rfl]
      iterate 2 twp_pure
      rw [pred_cast r hr]
      isimp only [stepCredit, nextCredit, nextRemaining] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      simp only [ClosedExp.openRec, Exp.ofVal]
      twp_bind pl(&(loop s ws) #int ((r - 1 : ℕ) : ℤ) &(NatCounters.encode acc).fst)
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %(r - 1) %acc %hlen %F Hcredit
    | succ i =>
      have hi : i < acc.length := by simp only [List.length_cons] at hcategory; omega
      rw [decide_eq_false (by omega : i + 1 ≠ 0)]
      iterate 2 twp_pure
      rw [pred_cast (i + 1) (Nat.succ_pos i), Nat.add_sub_cancel_right]
      isimp only [stepCredit, nextCredit, nextRemaining] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      simp only [ClosedExp.openRec]
      twp_bind pl(&Occil.DiscreteExtra.incrementCounter &(NatCounters.encode acc).fst
        #int (i : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply NatCounters.twp_incrementCounter E acc i hi
      iintro %v %hv
      subst v
      simp only [Exp.ofVal]
      twp_bind pl(&(loop s ws) #int (r : ℤ) &(NatCounters.encode (increment acc i)).fst)
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %r %(increment acc i) %(by simpa [increment] using hlen) %F Hcredit

private theorem twp_loop (E : CoPset) (r s : ℕ) (ws acc : List ℕ) (hs : 0 < s)
    (hlen : acc.length = ws.length) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit r s ws acc F) -∗
      tglWp E pl(&(loop s ws) #int (r : ℤ) &(NatCounters.encode acc).fst)
        (fun v : Val rT => iprop(∃ cs : List ℕ,
          ⌜v = NatCounters.encode cs⌝ ∗ ↯ (F cs))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  obtain ⟨δ, hδ, hbudget⟩ := termination_credit ε hε r
  isimp only [hbudget] at Hterm
  ihave ⟨Hextra, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hextra as Hcredit
  iapply (twp_loop_amplification E s ws hs δ hδ) $$ Hterm %r %acc %hlen %F Hcredit

/-- Categorical successes stop the loop; failure categories accumulate their own counts. -/
theorem twp_negativeMultinomial (E : CoPset) (r s : ℕ) (ws : List ℕ) (hs : 0 < s)
    (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ cs, F cs ∂law r s ws) -∗
      tglWp E pl(&Occil.DiscreteExtra.negativeMultinomial #int (r : ℤ)
        #int (s : ℤ) &(NatCounters.encode ws).fst)
        (fun v : Val rT => iprop(∃ cs : List ℕ,
          ⌜v = NatCounters.encode cs⌝ ∗ ↯ (F cs))) := by
  iintro Hcredit
  twp_pures
  rw [guard_test s hs]
  iterate 2 twp_pure
  twp_bind pl(&validate &(NatCounters.encode ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_validate E ws
  iintro %v %hv
  subst v
  iterate 3 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.length &(NatCounters.encode ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E (fun k : ℕ => Val.int (k : ℤ)) ws
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.DiscreteExtra.zeroCounters #int (ws.length : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply NatCounters.twp_zeroCounters E ws.length
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&(loop s ws) #int (r : ℤ)
    &(NatCounters.encode (List.replicate ws.length 0)).fst)
  iapply (tglWp_mono fun _ => tglWp_value)
  isimp only [← credit_initial r s ws F] at Hcredit
  iapply twp_loop E r s ws (List.replicate ws.length 0) hs (by simp) F $$ Hcredit

/-- Typed negative-multinomial law, including zero requests and absent failure categories. -/
theorem negativeMultinomial_distSpec (E : CoPset) (r s : ℕ) (ws : List ℕ) (hs : 0 < s) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.negativeMultinomial #int (r : ℤ)
      #int (s : ℤ) &(NatCounters.encode ws).fst) (law r s ws) NatCounters.encode where
  spec F _ := wand_entails (twp_negativeMultinomial E r s ws hs F)

end specification

end

end SampLib.NegativeMultinomial
