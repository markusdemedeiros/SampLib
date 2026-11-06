import SampLib.Discrete.Laws.FisherMultivariate
import SampLib.Discrete.BinomialBinary
import SampLib.Discrete.Support.NatUrnOps
import SampLib.Discrete.Syntax.Urns
import SampLib.Core.ProofMode.BindFrom

/-! # Multivariate Fisher sampling by conditioning independent binomials

The proposal builder samples each component once. The accepted-proposal rule
then conditions their sum on the requested draw count, with exact endpoint laws.
-/

open ProbLang
open scoped ENNReal NNReal SampLib.UrnTerms

namespace SampLib.FisherMultivariate

noncomputable section

private instance binary_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.binomialBinary : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.DiscreteExtra.binomialBinary, ClosedExp.closeRec, Exp.fv, ClosedExp.fv]

-- Finalize structural binders before inserting the closed, verified binomial sampler.
@[pl_fold] private def proposals {rT : Type _} : Exp rT :=
  .fix (.lam (.lam (.case (.bvar 1)
    (.lam (.inl (.lit .unit)))
    (.lam (.case (.bvar 1) (.lam .fail)
      (.lam (.app (.lam (.inr (.pair (.bvar 0)
        (.app (.app (.bvar 5) (.snd (.bvar 2))) (.snd (.bvar 1))))))
        (.app (.app (.app Occil.DiscreteExtra.binomialBinary (.fst (.bvar 1)))
          (.fst (.bvar 0))) (.binop .plus (.fst (.bvar 0)) (.lit (.int 1)))))))))))

private instance proposals_closed {rT : Type _} : ClosedExp (proposals : Exp rT) where
  lc := by is_lc
  fv := by simp [proposals, Exp.fv, ClosedExp.fv]

-- Insert the fixed population only after the recursive binders are finalized.
@[pl_fold] private def loop {rT : Type _} [ProbLangℝ rT] (draws : ℕ)
    (counts odds : List ℕ) : Exp rT :=
  .fix (.lam (.app (.lam (.cond
    (.binop .eq (.app Occil.sumInts (.bvar 0)) (.lit (.int draws))) (.bvar 0)
    (.app (.bvar 2) (.lit .unit))))
    (.app (.app proposals (NatCounters.encode counts).fst) (NatCounters.encode odds).fst)))

private instance loop_closed {rT : Type _} [ProbLangℝ rT] (draws : ℕ)
    (counts odds : List ℕ) : ClosedExp (loop (rT := rT) draws counts odds) where
  lc := by is_lc
  fv := by simp [loop, Exp.fv, ClosedExp.fv]

private theorem natural_test {rT : Type _} [BEq rT] (a b : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int (b : ℤ)) = decide (a = b) := by
  change decide ((a : ℤ) = (b : ℤ)) = decide (a = b)
  exact decide_eq_decide.mpr (by omega)

private theorem zero_test {rT : Type _} [BEq rT] (a : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int 0) = decide (a = 0) := by
  change decide ((a : ℤ) = 0) = decide (a = 0)
  exact decide_eq_decide.mpr (by omega)

private theorem request_test (draws : ℕ) (counts : List ℕ) (h : draws ≤ counts.sum) :
    decide ((counts.sum : ℤ) < (draws : ℤ)) = false :=
  decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem cons_value {rT : Type _} [ProbLangℝ rT] (x : ℕ) (xs : List ℕ) :
    pl(inr((#int (x : ℤ), {Exp.ofVal (NatCounters.encode xs)}))) =
      Exp.ofVal (NatCounters.encode (x :: xs) : Val rT) := rfl

private abbrev factor (draws : ℕ) (counts odds : List ℕ) : ℝ≥0 :=
  AcceptedProposal.factor (proposal counts odds) (acceptance draws)

private abbrev kernel (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) (F : List ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :=
  AcceptedProposal.kernel (proposal counts odds) (acceptance draws)
    (mass_nonzero draws counts odds hlen hodds hdraws) F ε

section mathematics

open MeasureTheory

private theorem kernel_eq (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) (F : List ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (xs : List ℕ) :
    kernel draws counts odds hlen hodds hdraws F ε xs =
      if xs.sum = draws then F xs else
        (∫⁻ ys, F ys ∂law draws counts odds hlen hodds hdraws) + factor draws counts odds * ε := by
  by_cases h : xs.sum = draws <;>
    simp [kernel, AcceptedProposal.kernel, AcceptedProposal.weight, AcceptedProposal.rejectedWeight,
      AcceptedProposal.credit, law, factor, h]

/-- The canonical accepted-law credit pays for either acceptance or amplified retry. -/
private theorem expectation (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) (F : List ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ xs, kernel draws counts odds hlen hodds hdraws F ε xs ∂proposal counts odds ≤
      (∫⁻ ys, F ys ∂law draws counts odds hlen hodds hdraws) + ε := by
  simpa only [kernel, AcceptedProposal.credit, law] using
    AcceptedProposal.expectation_preservation (proposal counts odds) (acceptance draws)
      (measurable_acceptance draws) (mass_nonzero draws counts odds hlen hodds hdraws)
      F (measurable_of_countable _) ε

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem proposals_distSpec (E : CoPset) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) :
    IsDistSpec (GF := GF) E pl(&proposals &(NatCounters.encode counts).fst
      &(NatCounters.encode odds).fst) (proposal counts odds) NatCounters.encode := by
  induction counts generalizing odds with
  | nil =>
    constructor
    intro F _
    iintro Hcredit
    isimp only [proposal, MeasureTheory.lintegral_dirac] at Hcredit
    simp only [NatCounters.encode, listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    iframe Hcredit
    ipureintro
    rfl
  | cons c cs IH =>
    cases odds with
    | nil => simp at hlen
    | cons o os =>
      have ht : cs.length = os.length := by simpa using hlen
      constructor
      intro F _
      iintro Hcredit
      isimp only [← proposal_cons c o cs os F] at Hcredit
      simp only [NatCounters.encode, listVal]
      iterate 11 twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&Occil.DiscreteExtra.binomialBinary #int (c : ℤ)
        #int (o : ℤ) #int ((o + 1 : ℕ) : ℤ))
      iapply ((BinomialBinary.binomialBinary_distSpec E c o (o + 1)
        (Nat.succ_pos o) (Nat.le_succ o)).wp
        (fun x => ∫⁻ xs, F (x :: xs) ∂proposal cs os) (measurable_of_countable _) _) $$ Hcredit
      iintro %x Hcredit
      iterate 3 twp_pure
      have hnext := (IH os ht).spec (fun xs => F (x :: xs)) (measurable_of_countable _)
      simp only [NatCounters.encode] at hnext
      twp_bind_from hnext
      iapply tglWp_wand
      isplitl [Hcredit]
      · exact hnext
      iintro %v ⟨%xs, %hv, Hcredit⟩
      subst v
      rw [cons_value]
      iapply (tglWp_value (v := NatCounters.encode (x :: xs)))
      iexists x :: xs
      iframe Hcredit
      itrivial

private theorem twp_loop (E : CoPset) (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law draws counts odds hlen hodds hdraws) -∗
      tglWp E pl(&(loop draws counts odds) #())
        (fun v : Val rT => iprop(∃ xs : List ℕ,
          ⌜v = NatCounters.encode xs⌝ ∗ ↯ (F xs))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor (proposal counts odds) (acceptance draws)
      (mass_nonzero draws counts odds hlen hodds hdraws)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(&proposals &(NatCounters.encode counts).fst &(NatCounters.encode odds).fst)
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken (expectation draws counts odds hlen hodds hdraws F ε)
    $$ Htotal
  iapply ((proposals_distSpec E counts odds hlen).wp
    (kernel draws counts odds hlen hodds hdraws F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %xs Hcredit
  twp_pure
  twp_bind pl(&Occil.sumInts &(NatCounters.encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E xs
  iintro %v %hv
  subst v
  twp_pure
  rw [natural_test]
  by_cases h : xs.sum = draws
  · rw [decide_eq_true h]
    isimp only [kernel_eq, ite_eq_left h] at Hcredit
    twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (NatCounters.encode xs)))
    iexists xs
    iframe Hcredit
    itrivial
  · rw [decide_eq_false h]
    isimp only [kernel_eq, ite_eq_right h] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&(loop draws counts odds) #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit

/-- Exact multivariate Fisher counts on the full finite positive-odds urn domain. -/
theorem fisherMultivariate_distSpec (E : CoPset) (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.fisherMultivariate #int (draws : ℤ)
      &(NatCounters.encode counts).fst &(NatCounters.encode odds).fst)
      (law draws counts odds hlen hodds hdraws) NatCounters.encode where
  spec F _ := by
    have hvalid := NatUrnOps.twp_validUrn (rT := rT) (GF := GF) E counts odds hlen hodds
    iintro Hcredit
    iterate 3 twp_pure
    twp_bind pl(&Occil.sumInts &(NatCounters.encode counts).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E counts
    iintro %v %hv
    subst v
    twp_pures
    rw [request_test draws counts hdraws, Bool.false_or]
    twp_pure
    twp_bind pl(&Occil.DiscreteExtra.validUrn &(NatCounters.encode counts).fst
      &(NatCounters.encode odds).fst)
    iapply tglWp_wand
    isplitl []
    · iapply hvalid
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [zero_test draws]
    by_cases hzero : draws = 0
    · subst draws
      rw [decide_eq_true rfl]
      isimp only [law_zero, MeasureTheory.lintegral_dirac] at Hcredit
      twp_pure
      twp_bind pl(&Occil.length &(NatCounters.encode counts).fst)
      iapply tglWp_wand
      isplitl []
      · iapply twp_length E _ counts
      iintro %v %hv
      subst v
      twp_bind pl(&Occil.DiscreteExtra.zeroCounters #int (counts.length : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply NatCounters.twp_zeroCounters E counts.length
      iintro %v %hv
      subst v
      iapply (tglWp_value (v := NatCounters.encode (List.replicate counts.length 0)))
      iexists List.replicate counts.length 0
      iframe Hcredit
      itrivial
    · rw [decide_eq_false hzero]
      twp_pure
      twp_pure
      rw [natural_test draws counts.sum]
      by_cases hfull : draws = counts.sum
      · subst draws
        rw [decide_eq_true rfl]
        isimp only [law_full, MeasureTheory.lintegral_dirac] at Hcredit
        twp_pure
        iapply (tglWp_value_of_toVal (Val.toVal?_fst (NatCounters.encode counts)))
        iexists counts
        iframe Hcredit
        itrivial
      · rw [decide_eq_false hfull]
        iterate 3 twp_pure
        twp_bind pl(&(loop draws counts odds) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply twp_loop E draws counts odds hlen hodds hdraws F $$ Hcredit

end specification

end

end SampLib.FisherMultivariate
