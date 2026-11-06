import SampLib.Uniform.Laws.RndIntExcRange

/-! # Almost-sure bounds for uniform integer proposals -/

namespace SampLib

open MeasureTheory MeasureTheory.Measure

namespace RndIntExcRange

/-- Translation transports the rank support to the half-open proposal interval. -/
theorem ae_mem (lower upper : ℤ) (h : lower < upper) :
    ∀ᵐ z ∂law lower upper h, z ∈ Set.Ico lower upper := by
  rw [law]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    measurableSet_Ico).2
  apply (UniformInt.ae_lt (upper - lower).toNat).mono
  intro k hk
  have hwidth : ((upper - lower).toNat : ℤ) = upper - lower :=
    Int.toNat_of_nonneg (sub_nonneg.mpr h.le)
  constructor <;> omega

end RndIntExcRange

end SampLib
