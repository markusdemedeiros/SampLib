import SampLib.Samplers.WeightedChoice

/-! # The categorical singleton shortcut, with arbitrary infinite credits -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.OptimalMatrix

/-- A single positive weight returns its sole label with probability one. -/
theorem singleton_credit (w : ℕ) (hw : 0 < w) (F : ℕ → ℝ≥0∞) :
    (∫⁻ i, F i ∂WeightedChoice.law [w]) = F 0 := by
  rw [WeightedChoice.lintegral_law]
  simp only [WeightedChoice.weightedSum, List.sum_singleton, add_zero]
  rw [mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hw.ne') (by finiteness)]

end SampLib.OptimalMatrix
