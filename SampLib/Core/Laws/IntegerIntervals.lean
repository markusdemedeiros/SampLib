import SampLib.Uniform.RndIntExcRange

/-! # Almost-sure bounds for uniform integer proposals -/

namespace SampLib

open MeasureTheory MeasureTheory.Measure

namespace UniformInt

/-- Uniform ranks lie in their finite range, including the empty zero measure. -/
theorem ae_lt (n : ℕ) : ∀ᵐ k ∂law n, k < n := by
  apply ae_iff_of_countable.mpr
  intro k hk
  by_contra h
  apply hk
  simp [law, uniformOfFinset_apply_singleton, Finset.mem_range, h]

end UniformInt

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
