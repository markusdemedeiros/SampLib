module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! # Credit arithmetic for retry loops

A retry loop runs one round. The round either accepts and pays its output credit,
or rejects and pays the credit for another try. `kernel` assigns that credit to
each outcome. `lintegral_kernel_le` shows that a round preserves the expected
credit and also funds a retry credit amplified by a factor `k`, provided that
the rejection probability times `k` is at most one. `factor` gives a standard `k`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.Retry

noncomputable section

/-- Amplification factor `1 + a` for a round that accepts with probability `a`. -/
def factor (a : ℝ≥0∞) : ℝ≥0 := 1 + a.toNNReal

theorem one_lt_factor {a : ℝ≥0∞} (h0 : a ≠ 0) (htop : a ≠ ∞) : 1 < factor a :=
  lt_add_of_pos_right 1 (ENNReal.toNNReal_pos h0 htop)

/-- If a round accepts with probability `a` and rejects with probability `r`, then
`r * factor a ≤ 1`, since `r * (1 + a) ≤ r + a ≤ 1`. -/
theorem mul_factor_le_one {a r : ℝ≥0∞} (h : a + r ≤ 1) : r * factor a ≤ 1 := by
  have hr : r ≤ 1 := le_trans le_add_self h
  calc r * factor a = r + r * a.toNNReal := by simp [factor, mul_add]
    _ ≤ r + a := by
        gcongr
        exact (mul_le_of_le_one_left zero_le hr).trans ENNReal.coe_toNNReal_le_self
    _ ≤ 1 := by rwa [add_comm]

variable {α : Type _} [MeasurableSpace α]

/-- Credit after one round: `A` on acceptance (`x ∈ s`), and `R` plus the retry
credit `δ` on rejection. -/
def kernel (s : Set α) [DecidablePred (· ∈ s)] (A R : α → ℝ≥0∞) (δ : ℝ≥0∞) (x : α) :
    ℝ≥0∞ :=
  if x ∈ s then A x else R x + δ

variable {μ : Measure α} {s : Set α} [DecidablePred (· ∈ s)]

/-- A round's expected credit: the accepted part, the rejected part, and the retry
credit weighted by the rejection probability. -/
theorem lintegral_kernel (hs : MeasurableSet s) (A R : α → ℝ≥0∞) (δ : ℝ≥0∞) :
    ∫⁻ x, kernel s A R δ x ∂μ = ∫⁻ x in s, A x ∂μ + ∫⁻ x in sᶜ, R x ∂μ + μ sᶜ * δ := by
  change ∫⁻ x, s.piecewise A (fun x => R x + δ) x ∂μ = _
  rw [lintegral_piecewise hs.nullMeasurableSet, lintegral_add_right _ measurable_const,
    setLIntegral_const, add_assoc, mul_comm]

/-- A round that preserves the expected credit `c` also funds a retry credit
amplified by `k`, once the rejection probability times `k` is at most one. -/
theorem lintegral_kernel_le (hs : MeasurableSet s) {A R : α → ℝ≥0∞} {c : ℝ≥0∞}
    {k : ℝ≥0} (hround : ∫⁻ x in s, A x ∂μ + ∫⁻ x in sᶜ, R x ∂μ ≤ c)
    (hk : μ sᶜ * k ≤ 1) (ε : ℝ≥0∞) :
    ∫⁻ x, kernel s A R (k * ε) x ∂μ ≤ c + ε := by
  rw [lintegral_kernel hs, ← mul_assoc]
  exact add_le_add hround (mul_le_of_le_one_left zero_le hk)

end

end SampLib.Retry
