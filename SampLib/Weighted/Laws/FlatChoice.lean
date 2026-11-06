import SampLib.Discrete.Laws.WeightedChoice

/-! # The expanded categorical table

The table holds one entry per unit of weight. Its entries are the same consecutive blocks as
the categorical rank partition.
-/



namespace SampLib.FlatChoice

noncomputable section

/-- One entry per unit of weight, with labels counted from `offset`. -/
def table : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, offset => List.replicate w offset ++ table ws (offset + 1)

@[simp] theorem length_table (ws : List ℕ) (offset : ℕ) :
    (table ws offset).length = ws.sum := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih => simp [table, ih]

/-- Table lookup is precisely the category containing the uniform rank. -/
theorem lookup (ws : List ℕ) (offset k : ℕ) (hk : k < ws.sum) :
    (table ws offset)[k]?.getD 0 = offset + WeightedChoice.category ws k := by
  induction ws generalizing offset k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [table]
    by_cases h : k < w
    · rw [List.getElem?_append_left (by simpa using h)]
      simp [h, WeightedChoice.category]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
      simp only [List.length_replicate]
      rw [ih (offset + 1) (k - w) (by simp only [List.sum_cons] at hk; omega)]
      simp only [WeightedChoice.category, ite_eq_right h]
      omega

end

end SampLib.FlatChoice
