import SampLib.Discrete.WeightedChoice

/-! # Support of categorical sampling -/

namespace SampLib.WeightedChoice

open MeasureTheory

/-- A category drawn with the coefficient weights is an actual list position. -/
theorem ae_lt_length (ws : List ℕ) : ∀ᵐ i ∂law ws, i < ws.length := by
  apply ae_iff_of_countable.mpr
  intro i hi
  by_contra h
  apply hi
  simp [law_singleton, List.getElem?_eq_none (Nat.le_of_not_gt h)]

end SampLib.WeightedChoice
