import SampLib.Uniform.UniformInt

/-! # Images of a finite uniform word

The mass of an output is its number of preimages divided by the source width.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.FiniteImage

noncomputable section

/-- Push a uniform source word through a deterministic integer transformation. -/
def law (width : ℕ) (f : ℕ → ℕ) : Measure ℕ :=
  (UniformInt.law width).map f

instance (width : ℕ) [NeZero width] (f : ℕ → ℕ) : IsProbabilityMeasure (law width f) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Transport continuation credit along the deterministic image. -/
theorem expectation (width : ℕ) (f : ℕ → ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F (f k) ∂UniformInt.law width = ∫⁻ x, F x ∂law width f := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- A deterministic transformation preserves expectation by composition. -/
theorem lintegral_law (width : ℕ) (f : ℕ → ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ x, F x ∂law width f = (∑ k ∈ range width, F (f k)) / width := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law]

/-- Collisions are counted exactly, including outputs outside the image. -/
theorem law_singleton (width : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    law width f {x} = ((range width).filter (fun k => f k = x)).card / (width : ℝ≥0∞) := by
  rw [← lintegral_indicator_one (measurableSet_singleton x), lintegral_law]
  simp [Set.indicator, sum_boole]

end

end SampLib.FiniteImage
