module

public import SampLib.Core.Laws.Retry
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-! # Conditioning a proposal law on a measurable acceptance set

Accepted proposals keep their credit. The rejected mass funds the amplified retry
credit.
-/

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

theorem one_lt_terminationFactor (hmass : μ s ≠ 0) :
    1 < terminationFactor μ s := by
  exact lt_add_of_pos_right 1 (ENNReal.toNNReal_pos hmass (measure_ne_top μ s))

/-- Expected continuation credit under the conditional law. -/
def credit (hmass : μ s ≠ 0) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, F x ∂law μ s hmass

variable [DecidablePred (· ∈ s)]

/-- Accepted proposals return; rejected proposals carry amplified retry credit. -/
def kernel (hmass : μ s ≠ 0) (F : α → ℝ≥0∞) (ε : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  if x ∈ s then F x else credit μ s hmass F + terminationFactor μ s * ε

omit [IsProbabilityMeasure μ] in
theorem measurable_kernel (hs : MeasurableSet s) (hmass : μ s ≠ 0)
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
  refine Retry.lintegral_kernel_le (R := fun _ => credit μ s hmass F) hs (le_of_eq ?_)
    (Retry.mul_factor_le_one (prob_add_prob_compl hs).le) ε
  rw [hcredit, setLIntegral_const, mul_comm (credit μ s hmass F), ← add_mul,
    prob_add_prob_compl hs, one_mul]

end mathematics

end

end SampLib.Rejection
