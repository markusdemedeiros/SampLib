import SampLib.Combinatorial.Laws.Choice
import SampLib.General.Laws.ListMapSampling

/-! # Vector kernel density law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.KernelDensityVector

noncomputable section

/-- Translate the scalar kernel to one center coordinate. -/
def offsetLaw (kernel : Measure ℤ) (x : ℤ) : Measure ℤ := kernel.map (x + ·)

instance (kernel : Measure ℤ) [IsProbabilityMeasure kernel] (x : ℤ) :
    IsProbabilityMeasure (offsetLaw kernel x) where
  measure_univ := by
    rw [offsetLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Choose one empirical vector, then perturb its coordinates independently. -/
def law (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ) :
    Measure (List ℤ) :=
  (Choice.law xs.length).bind (fun i => ListMapSampling.law (offsetLaw kernel) (xs.get i))

instance (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] : IsProbabilityMeasure (law xs kernel) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Retaining the common center preserves its dependence across coordinates. -/
theorem expectation (xs : List (List ℤ)) [NeZero xs.length] (kernel : Measure ℤ)
    [IsProbabilityMeasure kernel] (F : List ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ ys, F ys ∂ListMapSampling.law (offsetLaw kernel) (xs.get i)
      ∂Choice.law xs.length = ∫⁻ ys, F ys ∂law xs kernel := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end

end SampLib.KernelDensityVector
