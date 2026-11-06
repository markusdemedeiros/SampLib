import SampLib.Weighted.Laws.PowerOfTwoCeiling
import SampLib.Common.Laws.UniformRejection
import SampLib.Uniform.Laws.UniformInt

/-! # Expectation for bitmask rejection

A full word at the least enclosing power of two is accepted with probability at least
one half, so rejected words fund the retry with doubled credit.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.BitmaskRejection

noncomputable section

/-- Uniform word proposals preserve the target credit and fund bounded rejection. -/
theorem expectation (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ k, UniformRejection.kernel n F ε k
      ∂UniformInt.law (PowerOfTwoCeiling.width n) ≤
      (∫⁻ k, F k ∂UniformInt.law n) + ε := by
  rw [UniformInt.lintegral_law]
  exact UniformRejection.expectation n _ hn (PowerOfTwoCeiling.le_width n)
    (PowerOfTwoCeiling.width_le_double n hn) F ε

end

end SampLib.BitmaskRejection
