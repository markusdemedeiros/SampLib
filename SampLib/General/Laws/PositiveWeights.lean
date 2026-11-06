import SampLib.Common.Laws.WeightedSupport

/-! # Positive categorical weights on almost every selected category -/

namespace SampLib.WeightedChoice

open MeasureTheory

/-- Zero-weight categories are never selected. -/
theorem ae_getD_pos (weights : List ℕ) :
    ∀ᵐ i ∂law weights, 0 < weights[i]?.getD 0 := by
  apply ae_iff_of_countable.mpr
  intro i hi
  by_contra h
  have hz : weights[i]?.getD 0 = 0 := by omega
  apply hi
  simp [law_singleton, hz]

end SampLib.WeightedChoice
