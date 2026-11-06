import SampLib.Discrete.WeightedChoice

/-! # Positive support of categorical sampling -/

namespace SampLib.WeightedChoice

open MeasureTheory

/-- Zero-weight categories are absent even when continuation credits there are infinite. -/
theorem ae_pos_weight (ws : List ℕ) : ∀ᵐ i ∂law ws, 0 < ws[i]?.getD 0 := by
  apply ae_iff_of_countable.mpr
  intro i hi
  by_contra h
  apply hi
  simp [law_singleton, Nat.eq_zero_of_not_pos h]

end SampLib.WeightedChoice
