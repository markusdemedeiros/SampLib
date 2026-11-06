import SampLib.Distributions.BinomialBinary
import SampLib.Samplers.BinomialHalfBits
import SampLib.SupportedSpec
import SampLib.Syntax.ClosedExp
import Metrology.Iris.LocalBI

/-! # Binary expansion of a rational binomial bias

A fair-binomial split resolves half the trials on average. Conditional thinning
preserves the binomial law; the shrinking unresolved population pays for the
fixed amplification used by the CTE termination induction.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.BinomialBinary

noncomputable section

private def loop {rT : Type _} (denominator : ℕ) : Exp rT := pl%
  rec go remaining remainder successes :=
    if (remaining = #0) || (remainder = #0) then successes else
      let half := &Occil.DiscreteExtra.binomialHalfBits remaining;
      let twice := #2 * remainder;
      if #int (denominator : ℤ) <= twice then
        go (remaining - half) (twice - #int (denominator : ℤ)) (successes + half)
      else go half twice successes

private instance halfBits_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.binomialHalfBits : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.DiscreteExtra.binomialHalfBits, Occil.DiscreteExtra.integerPower,
      Occil.uniformInt, Exp.fv]

private theorem zero_test {rT : Type _} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = decide (n = 0) := by
  change decide ((n : ℤ) = 0) = decide (n = 0)
  exact decide_eq_decide.mpr (by omega)

private theorem stop_test (n a : ℕ) :
    Bool.or (decide (n = 0)) (decide (a = 0)) = decide (n = 0 ∨ a = 0) := by
  simp

private theorem high_test (a b : ℕ) :
    decide ((b : ℤ) ≤ 2 * a) = decide (b ≤ 2 * a) := by
  exact decide_eq_decide.mpr (by omega)

private theorem double_cast (a : ℕ) : (2 : ℤ) * a = ((2 * a : ℕ) : ℤ) := by
  norm_cast

private theorem difference_cast (a b : ℕ) (h : b ≤ a) :
    (a : ℤ) - b = ((a - b : ℕ) : ℤ) := (Nat.cast_sub h).symm

private theorem termination_credit (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ε = n * δ + δ := by
  refine ⟨ε / (n + 1), ENNReal.div_pos hε.ne' (by finiteness), ?_⟩
  have h : ε / (n + 1) * (n + 1) = ε :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one, mul_comm (ε / (n + 1))] at h
  exact h.symm

private theorem domain_test (a b : ℕ) (hb : 0 < b) (ha : a ≤ b) :
    Bool.or (Bool.or (Bool.or false (decide ((b : ℤ) ≤ 0))) false)
      (decide ((b : ℤ) < a)) = false := by
  simp [Nat.ne_of_gt hb, show ¬(b : ℤ) < a by omega]

private theorem full_test {rT : Type _} [BEq rT] (a b : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int (b : ℤ)) = decide (a = b) := by
  change decide ((a : ℤ) = (b : ℤ)) = decide (a = b)
  exact decide_eq_decide.mpr (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop_amplification (E : CoPset) (b : ℕ) (hb : 0 < b)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ n : ℕ, ∀ a : ℕ, ∀ successes : ℕ, ⌜a < b⌝ -∗ ∀ F : ℕ → ℝ≥0∞,
      ↯ ((∫⁻ k, F (successes + k) ∂law n a b) + n * δ) -∗
      tglWp E pl(&(loop b) #int (n : ℤ) #int (a : ℤ) #int (successes : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple hδ one_lt_factor $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %n %a %successes %ha %F Hcredit
  iterate 5 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  rw [zero_test a]
  twp_pure
  rw [zero_test n]
  twp_pure
  rw [stop_test]
  by_cases hstop : n = 0 ∨ a = 0
  · rw [decide_eq_true hstop]
    twp_pures
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    isimp only [expectation_stop n a b successes F hstop] at Hcredit
    twp_value
    imodintro
    iexists successes
    iframe Hcredit
    itrivial
  · have hn : 0 < n := by omega
    rw [decide_eq_false hstop]
    twp_pure
    twp_bind pl(&Occil.DiscreteExtra.binomialHalfBits #int (n : ℤ))
    icombine Hcredit Hterm as Hcredit
    ihave Hcredit := ErrorCredit.weaken
      (expectation_preservation n a b successes hb ha hn F δ)
      $$ Hcredit
    iapply ((BinomialHalfBits.binomialHalfBits_distSpec E n).wp_supported
      (fun half => half ≤ n) ((Set.to_countable _).measurableSet)
      (Binomial.support VonNeumann.fairBias n)
      (refinementCredit n a b successes F δ)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %half %hhalf Hcredit
    iterate 4 twp_pure
    simp only [ClosedExp.openRec]
    rw [high_test a b]
    by_cases h : b ≤ 2 * a
    · rw [decide_eq_true h]
      isimp only [refinementCredit, ite_eq_left h] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      iterate 3 twp_pure
      rw [double_cast, difference_cast (2 * a) b h,
        difference_cast n half hhalf, ← Nat.cast_add]
      twp_bind pl(&(loop b) #int ((n - half : ℕ) : ℤ)
        #int ((2 * a - b : ℕ) : ℤ) #int ((successes + half : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %(n - half) %(2 * a - b) %(successes + half)
        %(by omega) %F Hcredit
    · rw [decide_eq_false h]
      isimp only [refinementCredit, ite_eq_right h] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      rw [double_cast]
      twp_bind pl(&(loop b) #int (half : ℤ) #int ((2 * a : ℕ) : ℤ)
        #int (successes : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %half %(2 * a) %successes %(by omega) %F Hcredit

private theorem twp_loop (E : CoPset) (n a b successes : ℕ) (hb : 0 < b) (ha : a < b)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F (successes + k) ∂law n a b) -∗
      tglWp E pl(&(loop b) #int (n : ℤ) #int (a : ℤ) #int (successes : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  obtain ⟨δ, hδ, hbudget⟩ := termination_credit ε hε n
  isimp only [hbudget] at Hterm
  ihave ⟨Hextra, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hextra as Hcredit
  iapply (twp_loop_amplification E b hb δ hδ) $$ Hterm %n %a %successes %ha %F Hcredit

/-- Exact rational binomial sampling by fair binary refinement, including both endpoints. -/
theorem twp_binomialBinary (E : CoPset) (n a b : ℕ) (hb : 0 < b) (ha : a ≤ b)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n a b) -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialBinary #int (n : ℤ)
        #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iterate 10 twp_pure
  rw [domain_test a b hb ha]
  iterate 2 twp_pure
  rw [full_test a b]
  by_cases hab : a = b
  · subst a
    rw [decide_eq_true (show b = b from rfl)]
    twp_pures
    isimp only [law, bias_full b hb, Binomial.law_one, MeasureTheory.lintegral_dirac] at Hcredit
    twp_value
    imodintro
    iexists n
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hab]
    iterate 2 twp_pure
    have h := twp_loop (rT := rT) (GF := GF) E n a b 0 hb (by omega) F
    simp only [Nat.zero_add] at h
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind pl(&(loop b) #int (n : ℤ) #int (a : ℤ) #0)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply h $$ Hcredit

/-- Reusable binomial law for every valid rational success probability. -/
theorem binomialBinary_distSpec (E : CoPset) (n a b : ℕ) (hb : 0 < b) (ha : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.binomialBinary #int (n : ℤ)
      #int (a : ℤ) #int (b : ℤ)) (law n a b) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_binomialBinary E n a b hb ha F)

end specification

end

end SampLib.BinomialBinary
