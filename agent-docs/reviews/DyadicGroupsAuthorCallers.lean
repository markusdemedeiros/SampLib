import SampLib.Distributions.DyadicGroups

open Finset
open scoped ENNReal

namespace DyadicGroupsAuthor

open SampLib.DyadicGroups

example {A : Type*} [AddCommMonoid A] (n : ℕ) (F : ℕ → A) :
    (∑ k ∈ range n.size, ∑ r ∈ range (width n k), F (lower k - 1 + r)) =
      ∑ i ∈ range n, F i := sum_groups n F

example : (List.range (Nat.size 8)).map (width 8) = [1, 2, 4, 1] := by decide
example : (List.range (Nat.size 7)).map (width 7) = [1, 2, 4] := by decide
example : (List.range (Nat.size 9)).map (width 9) = [1, 2, 4, 2] := by decide
example : (List.range (Nat.size 1)).map (width 1) = [1] := by decide
example : (List.range (Nat.size 0)).map (width 0) = [] := by decide

example (F : ℕ → ℝ≥0∞) :
    (∑ k ∈ range (Nat.size 8), ∑ r ∈ range (width 8 k), F (lower k - 1 + r)) =
      ∑ i ∈ range 8, F i := sum_groups 8 F

example :
    (∑ k ∈ range (Nat.size 0), ∑ _r ∈ range (width 0 k), (∞ : ℝ≥0∞)) = 0 := by simp

example (k r : ℕ) (hk : k < (Nat.size 8)) (hr : r < width 8 k) : lower k - 1 + r < 8 :=
  offset_lt 8 k r hk hr

#print axioms SampLib.DyadicGroups.sum_groups
#print axioms SampLib.DyadicGroups.offset_lt
#print axioms SampLib.DyadicGroups.width_eq_cutoff

end DyadicGroupsAuthor
