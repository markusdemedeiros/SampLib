import SampLib.General.Laws.StoppedSum

/-! # Stopped sum with its count -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Episodes

noncomputable section

/-- Keep the stopping count in the joint law of the random sum. -/
def law (ν : Measure ℕ) (μ : Measure ℤ) : Measure (ℤ × ℕ) :=
  ν.bind (fun n => (StoppedSum.sumLaw μ n).map (fun z => (z, n)))

instance (ν : Measure ℕ) [IsProbabilityMeasure ν] (μ : Measure ℤ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (law ν μ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp [Measure.map_apply (measurable_of_countable _)]

/-- The sum is conditioned on the very count retained in the returned pair. -/
theorem expectation (ν : Measure ℕ) [IsProbabilityMeasure ν] (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (F : ℤ × ℕ → ℝ≥0∞) :
    ∫⁻ n, ∫⁻ z, F (z, n) ∂StoppedSum.sumLaw μ n ∂ν =
      ∫⁻ p, F p ∂law ν μ := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp only [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end

end SampLib.Episodes
