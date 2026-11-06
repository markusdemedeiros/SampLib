module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat

/-! # Finite integer Fisher weights -/

public section

namespace SampLib.FisherHypergeometric

/-- Integer weights clear the common odds denominator. -/
def weight (n ones zeros a b k : ℕ) : ℕ :=
  ones.choose k * zeros.choose (n - k) * a ^ k * b ^ (n - k)

/-- Include every potential marked-ball count; impossible counts have weight zero. -/
def table (n ones zeros a b : ℕ) : List ℕ :=
  (List.range (n + 1)).map (weight n ones zeros a b)

/-- Valid populations and positive odds give a nonzero normalization constant. -/
theorem total_pos (n ones zeros a b : ℕ) (hn : n ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) : 0 < (table n ones zeros a b).sum := by
  let k := min n ones
  have hk : k ≤ n := Nat.min_le_left _ _
  have ho : k ≤ ones := Nat.min_le_right _ _
  have hz : n - k ≤ zeros := by dsimp [k]; omega
  have hw : 0 < weight n ones zeros a b k := by
    exact mul_pos (mul_pos (mul_pos (Nat.choose_pos ho) (Nat.choose_pos hz))
      (pow_pos ha k)) (pow_pos hb (n - k))
  have hmem : weight n ones zeros a b k ∈ table n ones zeros a b := by
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  exact hw.trans_le (List.le_sum_of_mem hmem)

theorem table_get (n ones zeros a b k : ℕ) :
    ((table n ones zeros a b)[k]?.getD 0) =
      if k ≤ n then weight n ones zeros a b k else 0 := by
  by_cases h : k ≤ n
  · simp only [table, List.getElem?_map, List.getElem?_range (by omega : k < n + 1),
      Option.map_some, Option.getD_some, ite_eq_left h]
  · have hk : (List.range (n + 1))[k]? = none :=
      List.getElem?_eq_none (by simpa using (show n + 1 ≤ k by omega))
    simp only [table, List.getElem?_map, hk, Option.map_none, Option.getD_none, ite_eq_right h]

end SampLib.FisherHypergeometric
