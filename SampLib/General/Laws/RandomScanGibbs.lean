import SampLib.Combinatorial.Laws.Choice
import SampLib.General.Laws.FiniteKernels

/-! # Random-scan Gibbs kernel

A uniformly chosen coordinate kernel preserves every target that each coordinate kernel
preserves.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RandomScanGibbs

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- One coordinate is chosen uniformly, then its conditional kernel is applied. -/
def kernel (dimension : ℕ) [NeZero dimension] (K : Fin dimension → α → Measure α)
    (x : α) : Measure α :=
  (Choice.law dimension).bind (fun i => K i x)

instance (dimension : ℕ) [NeZero dimension] (K : Fin dimension → α → Measure α)
    [∀ i x, IsProbabilityMeasure (K i x)] (x : α) :
    IsProbabilityMeasure (kernel dimension K x) where
  measure_univ := by
    rw [kernel, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

abbrev law (dimension : ℕ) [NeZero dimension] (K : Fin dimension → α → Measure α) :=
  FiniteKernels.iterate (kernel dimension K)

/-- The coordinate choice and conditional draw give the mixed-kernel expectation. -/
theorem expectation (dimension : ℕ) [NeZero dimension] (K : Fin dimension → α → Measure α)
    (n : ℕ) (x : α) (F : α → ℝ≥0∞) :
    (∑ k ∈ Finset.range dimension,
      ∫⁻ y, (∫⁻ z, F z ∂law dimension K n y) ∂K (Choice.position dimension k) x) /
        dimension = ∫⁻ z, F z ∂law dimension K (n + 1) x := by
  rw [← Choice.lintegral_law dimension
    (fun i => ∫⁻ y, (∫⁻ z, F z ∂law dimension K n y) ∂K i x),
    ← FiniteKernels.expectation, kernel,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]

/-- A uniform mixture of invariant coordinate kernels preserves the same target. -/
theorem kernel_invariant (dimension : ℕ) [NeZero dimension]
    (K : Fin dimension → α → Measure α) (μ : Measure α) [IsProbabilityMeasure μ]
    (h : ∀ i, μ.bind (K i) = μ) : μ.bind (kernel dimension K) = μ := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  simp_rw [kernel, Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
  have hmass (i : Fin dimension) : (∫⁻ x, (K i x) s ∂μ) = μ s := by
    rw [← Measure.bind_apply hs (measurable_of_countable _).aemeasurable, h i]
  simp_rw [hmass]
  simp

/-- Any fixed number of random-scan updates preserves an invariant target. -/
theorem invariant (dimension : ℕ) [NeZero dimension]
    (K : Fin dimension → α → Measure α) (μ : Measure α) [IsProbabilityMeasure μ]
    (h : ∀ i, μ.bind (K i) = μ) (n : ℕ) : μ.bind (law dimension K n) = μ :=
  FiniteKernels.invariant _ μ (kernel_invariant dimension K μ h) n

end

end SampLib.RandomScanGibbs
