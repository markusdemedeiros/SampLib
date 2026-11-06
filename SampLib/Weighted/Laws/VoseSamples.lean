import SampLib.Combinatorial.Laws.SampleWithReplacement
import SampLib.Discrete.Laws.WeightedChoice

/-! # The law of independent categorical draws as a list -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.VoseSamples

noncomputable section

/-- The independent categorical vector, decoded as a list in sampling order. -/
def law (ws : List ℕ) (count : ℕ) : Measure (List ℕ) :=
  (SampleWithReplacement.law (WeightedChoice.law ws) count).map List.ofFn

instance (ws : List ℕ) [NeZero ws.sum] (count : ℕ) : IsProbabilityMeasure (law ws count) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem law_zero (ws : List ℕ) : law ws 0 = Measure.dirac [] := by
  simp [law, SampleWithReplacement.law]

/-- Decoding the independent vector preserves arbitrary list continuation credits. -/
theorem expectation (ws : List ℕ) (count : ℕ) (F : List ℕ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ xs, F (List.ofFn xs) ∂SampleWithReplacement.law (WeightedChoice.law ws) count =
      ∫⁻ ys, F ys ∂law ws count := by
  rw [law, lintegral_map hF (measurable_of_countable _)]

end

end SampLib.VoseSamples
