import SampLib.Combinatorial.Laws.Choice

/-! # Kernel density law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.KernelDensity

noncomputable section

/-- An empirical center and an independent kernel offset. -/
def law (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ) : Measure ℤ :=
  ((Choice.law xs.length).prod kernel).map (fun z => xs.get z.1 + z.2)

instance (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] : IsProbabilityMeasure (law xs kernel) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Conditioning on the empirical center gives its translated kernel expectation. -/
theorem expectation (xs : List ℤ) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ z, F (xs.get i + z) ∂kernel ∂Choice.law xs.length =
      ∫⁻ x, F x ∂law xs kernel := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.KernelDensity
