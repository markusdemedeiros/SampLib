import SampLib.Common.Laws.ListProduct
import SampLib.Uniform.Laws.UniformInt

/-! # Uniform box point law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.UniformBoxPoint

noncomputable section

/-- Independent coordinates in `[0,scale)`, in their returned order. -/
def law (scale dimension : ℕ) : Measure (List ℕ) :=
  ListProduct.law (fun _ => UniformInt.law scale) 0 dimension

instance (scale dimension : ℕ) [NeZero scale] : IsProbabilityMeasure (law scale dimension) :=
  inferInstanceAs (IsProbabilityMeasure
    (ListProduct.law (fun _ => UniformInt.law scale) 0 dimension))

/-- The tail and the new coordinate retain their independent product expectation. -/
theorem expectation (scale dimension : ℕ) [NeZero scale] (F : List ℕ → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂UniformInt.law scale ∂law scale dimension =
      ∫⁻ ys, F ys ∂law scale (dimension + 1) := by
  simpa only [law, ListProduct.constant_start] using
    ListProduct.expectation (fun _ => UniformInt.law scale) 0 dimension F

end

end SampLib.UniformBoxPoint
