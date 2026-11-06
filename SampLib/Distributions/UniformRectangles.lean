import SampLib.Distributions.WordIntervals

/-! # Flattening independent uniform digits

Two independent digits enumerate consecutive equal blocks of one uniform word.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.UniformRectangles

noncomputable section

/-- A high digit and a low digit form one uniform rectangular index. -/
theorem expectation (width copies : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, (∫⁻ j, F (width * i + j) ∂UniformInt.law width) ∂UniformInt.law copies =
      ∫⁻ k, F k ∂UniformInt.law (width * copies) := by
  simp_rw [UniformInt.lintegral_law, ENNReal.div_eq_inv_mul]
  rw [← mul_sum, WordIntervals.sum_blocks, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness))]
  ring

end

end SampLib.UniformRectangles
