import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Uniform.Laws.RndIntExcRange

/-! # Histogram law

A histogram chooses a bin by its integer mass and then a uniform integer inside that bin.
-/

open scoped ENNReal

namespace SampLib.Histogram

noncomputable section

open MeasureTheory Measure

/-- Select uniformly within a valid bin; the default lies outside categorical support. -/
def binLaw (points : List ℤ) (weights : List ℕ)
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0)
    (i : ℕ) : Measure ℤ :=
  if hi : i < weights.length then
    RndIntExcRange.law (points[i]?.getD 0) (points[i + 1]?.getD 0) (hwidth i hi)
  else dirac 0

instance (points : List ℤ) (weights : List ℕ)
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0)
    (i : ℕ) : IsProbabilityMeasure (binLaw points weights hwidth i) := by
  unfold binLaw
  split <;> infer_instance

/-- Bin counts are categorical masses, followed by an independent uniform position. -/
def law (points : List ℤ) (weights : List ℕ)
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0) :
    Measure ℤ := (WeightedChoice.law weights).bind (binLaw points weights hwidth)

instance (points : List ℤ) (weights : List ℕ) [NeZero weights.sum]
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0) :
    IsProbabilityMeasure (law points weights hwidth) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the chosen bin preserves the histogram expectation. -/
theorem expectation (points : List ℤ) (weights : List ℕ) [NeZero weights.sum]
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0)
    (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ z, F z ∂binLaw points weights hwidth i ∂WeightedChoice.law weights =
      ∫⁻ z, F z ∂law points weights hwidth := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end

end SampLib.Histogram
