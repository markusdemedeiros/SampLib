import SampLib.Discrete.WeightedChoice

/-! # Elementary identities for finite categorical expectations -/

open scoped ENNReal

namespace SampLib.WeightedChoice

theorem weightedSum_const (ws : List ℕ) (c : ℝ≥0∞) :
    weightedSum ws (fun _ => c) = ws.sum * c := by
  induction ws with
  | nil => simp [weightedSum]
  | cons w ws ih => simp [weightedSum, ih, add_mul]

/-- A zero-total block carries no credit, even for infinite continuation values. -/
theorem weightedSum_of_sum_zero (ws : List ℕ) (hs : ws.sum = 0) (F : ℕ → ℝ≥0∞) :
    weightedSum ws F = 0 := by
  induction ws generalizing F with
  | nil => rfl
  | cons w ws ih =>
    have hw : w = 0 := by simp only [List.sum_cons] at hs; omega
    have ht : ws.sum = 0 := by simp only [List.sum_cons] at hs; omega
    simp only [weightedSum, hw, Nat.cast_zero, zero_mul, zero_add]
    exact ih ht _

end SampLib.WeightedChoice
