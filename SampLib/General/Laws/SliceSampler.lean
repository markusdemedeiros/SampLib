import SampLib.General.Laws.Slice

/-! # Initialized slice sampler law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SliceSampler

noncomputable section

/-- One initialization transition, followed by the remaining grid transitions. -/
def initialLaw {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) : Measure (Fin width) :=
  (SliceLaw.stepLaw w cap hcap hanchor).bind (SliceLaw.law w n)

instance {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) :
    IsProbabilityMeasure (initialLaw w cap hcap hanchor n) where
  measure_univ := by
    rw [initialLaw, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

theorem initial_expectation {width : ℕ} (w : Fin width → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ i, cap ≤ w i) (n : ℕ) (F : Fin width → ℝ≥0∞) :
    ∫⁻ y, (∫⁻ z, F z ∂SliceLaw.law w n y) ∂SliceLaw.stepLaw w cap hcap hanchor =
      ∫⁻ z, F z ∂initialLaw w cap hcap hanchor n := by
  rw [initialLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end

end SampLib.SliceSampler
