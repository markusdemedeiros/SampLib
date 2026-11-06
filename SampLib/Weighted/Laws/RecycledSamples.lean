import SampLib.Combinatorial.Laws.SampleWithReplacement
import SampLib.Uniform.Laws.UniformInt

/-! # The law of independent uniform draws as a list -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RecycledSamples

noncomputable section

/-- Independent uniform draws on `[0,n)`, decoded as a list in sampling order. -/
def law (n count : ℕ) : Measure (List ℕ) :=
  (SampleWithReplacement.law (UniformInt.law n) count).map List.ofFn

instance (n count : ℕ) [NeZero n] : IsProbabilityMeasure (law n count) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Decoding the independent vector preserves arbitrary list continuation credits. -/
theorem expectation (n count : ℕ) (F : List ℕ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ xs, F (List.ofFn xs) ∂SampleWithReplacement.law (UniformInt.law n) count =
      ∫⁻ ys, F ys ∂law n count := by
  rw [law, lintegral_map hF (measurable_of_countable _)]

end

end SampLib.RecycledSamples
