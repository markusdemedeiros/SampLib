import SampLib.Templates
import Samplers.Continuous.Rejection
import Metrology.Iris.LocalBI

/-!
# Rejection on a measurable acceptance set

The target law is the proposal law conditioned on acceptance. Auxiliary credit
is amplified only when the sampled proposal is rejected.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.Rejection

noncomputable section

section mathematics

open MeasureTheory

variable {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (s : Set α)

/-- Proposal law conditioned on a positive-mass acceptance set. -/
def law (_hmass : μ s ≠ 0) : Measure α := (μ s)⁻¹ • μ.restrict s

instance (hmass : μ s ≠ 0) : IsProbabilityMeasure (law μ s hmass) where
  measure_univ := by
    simp [law, ENNReal.inv_mul_cancel hmass (measure_ne_top μ s)]

/-- A bounded amplification factor also handles acceptance mass one. -/
def terminationFactor : ℝ≥0 := 1 + (μ s).toNNReal

private theorem one_lt_terminationFactor (hmass : μ s ≠ 0) :
    1 < terminationFactor μ s := by
  exact lt_add_of_pos_right 1 (ENNReal.toNNReal_pos hmass (measure_ne_top μ s))

/-- Expected continuation credit under the conditional law. -/
def credit (hmass : μ s ≠ 0) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, F x ∂law μ s hmass

variable [DecidablePred (· ∈ s)]

/-- Accepted proposals return; rejected proposals carry amplified retry credit. -/
def kernel (hmass : μ s ≠ 0) (F : α → ℝ≥0∞) (ε : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  if x ∈ s then F x else credit μ s hmass F + terminationFactor μ s * ε

omit [IsProbabilityMeasure μ] in
private theorem measurable_kernel (hs : MeasurableSet s) (hmass : μ s ≠ 0)
    (F : α → ℝ≥0∞) (hF : Measurable F) (ε : ℝ≥0∞) :
    Measurable (kernel μ s hmass F ε) :=
  Measurable.ite hs hF measurable_const

/-- Conditioning conserves output credit; the rejected mass funds amplification. -/
theorem expectation_preservation (hs : MeasurableSet s) (hmass : μ s ≠ 0)
    (F : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ x, kernel μ s hmass F ε x ∂μ ≤ credit μ s hmass F + ε := by
  have hcredit : ∫⁻ x in s, F x ∂μ = μ s * credit μ s hmass F := by
    rw [credit, law, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hmass (measure_ne_top μ s), one_mul]
  have hamp : μ sᶜ * (terminationFactor μ s : ℝ≥0∞) ≤ 1 := by
    calc
      _ = μ sᶜ + μ sᶜ * μ s := by
        simp [terminationFactor, ENNReal.coe_toNNReal (measure_ne_top μ s), mul_add]
      _ ≤ μ sᶜ + μ s := by
        gcongr
        exact mul_le_of_le_one_left (show 0 ≤ μ s from zero_le) (prob_le_one (μ := μ))
      _ = 1 := by rw [add_comm, prob_add_prob_compl hs]
  calc
    _ = μ s * credit μ s hmass F +
        μ sᶜ * (credit μ s hmass F + terminationFactor μ s * ε) := by
      change ∫⁻ x, s.piecewise F (fun _ => _) x ∂μ = _
      rw [lintegral_piecewise hs.nullMeasurableSet, setLIntegral_const, hcredit]
      ring
    _ = credit μ s hmass F + (μ sᶜ * (terminationFactor μ s : ℝ≥0∞)) * ε := by
      calc
        _ = (μ s + μ sᶜ) * credit μ s hmass F +
            (μ sᶜ * (terminationFactor μ s : ℝ≥0∞)) * ε := by ring
        _ = _ := by rw [prob_add_prob_compl hs, one_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left (show 0 ≤ ε from zero_le) hamp)

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- CTE rejection spec for a verified proposal and deterministic acceptance test. -/
theorem twp_rejection (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal accept : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (haccept : ∀ x, ⊢ tglWp E pl(&accept.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (credit μ s hmass F) -∗
      tglWp E pl(&Occil.rejection &proposal.fst &accept.fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_terminationFactor μ s hmass) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&proposal.fst #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation μ s hs hmass F ε) $$ Hcredit
  iapply (hproposal.wp (kernel μ s hmass F ε) (measurable_kernel μ s hs hmass F hF ε) _)
    $$ Hcredit
  iintro %x Hcredit
  twp_pures
  twp_bind pl(&accept.fst &(encode x).fst)
  iapply tglWp_wand
  isplitl []
  · iapply haccept x
  iintro %v %hv
  subst v
  by_cases hx : x ∈ s
  · simp only [hx, decide_true]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode x)))
    iexists x
    isimp only [kernel, ite_eq_left hx] at Hcredit
    iframe Hcredit
    itrivial
  · simp only [hx, decide_false]
    twp_pure
    isimp only [kernel, ite_eq_right hx] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&Occil.rejection &proposal.fst &accept.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit

/-- Typed conditional output law. -/
theorem rejection_distSpec (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal accept : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (haccept : ∀ x, ⊢ tglWp E pl(&accept.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.rejection &proposal.fst &accept.fst #())
      (law μ s hmass) encode where
  spec F hF := wand_entails (twp_rejection E μ s hs hmass encode proposal accept
    hproposal haccept F hF)

end specification

end

end SampLib.Rejection
