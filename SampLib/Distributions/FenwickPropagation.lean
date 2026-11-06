module

public import SampLib.Distributions.Fenwick

@[expose] public section

/-! # Propagating a replacement through a Fenwick tree

Nodes below the current ancestor already contain their new sums. Between that
ancestor and its parent, every skipped node is unaffected by the replacement.
-/

namespace FenwickMath

/-- The partially updated tree immediately before visiting node `i`. -/
def partialTree {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value i : ℕ) : Fin (n + 1) → ℕ :=
  fun k => if k.val < i then cell (Function.update w j value) k.val else cell w k.val

theorem cell_update_of_not_contains {n : ℕ} (w : Fin n → ℕ) (j : Fin n)
    (value i : ℕ) (h : ¬ contains (j.val + 1) i) :
    cell (Function.update w j value) i = cell w i := by
  have he := cell_update_int w j value i
  simp only [h, ite_false, add_zero] at he
  exact_mod_cast he

theorem partialTree_initial {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ) :
    partialTree w j value (j.val + 1) = fun k => cell w k.val := by
  funext k
  simp only [partialTree]
  split_ifs with hk
  · exact cell_update_of_not_contains w j value k.val (by
      intro h
      have := h.2
      omega)
  · rfl

theorem partialTree_done {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value i : ℕ)
    (hi : n < i) :
    partialTree w j value i = fun k => cell (Function.update w j value) k.val := by
  funext k
  exact ite_eq_left (by have := k.isLt; omega)

theorem partialTree_current {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ)
    (i : Fin (n + 1)) : partialTree w j value i.val i = cell w i.val :=
  ite_eq_right (Nat.lt_irrefl _)

/-- One write accounts for the entire gap up to the next ancestor. -/
theorem partialTree_advance {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ)
    (i : Fin (n + 1)) (h : contains (j.val + 1) i.val) :
    Function.update (partialTree w j value i.val) i
        (cell (Function.update w j value) i.val) =
      partialTree w j value (i.val + lowBit i.val) := by
  have hi : 0 < i.val := by have := h.2; omega
  have hb := lowBit_pos hi
  funext k
  by_cases heq : k = i
  · subst k
    simp [partialTree, hb]
  · rw [Function.update_of_ne heq]
    simp only [partialTree]
    by_cases hk : k.val < i.val
    · rw [ite_eq_left hk, ite_eq_left (by omega)]
    · rw [ite_eq_right hk]
      split_ifs with hk'
      · symm
        apply cell_update_of_not_contains
        apply not_contains_between h (by have := Fin.val_ne_of_ne heq; omega) hk'
      · rfl

theorem propagation_measure {n i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    n + 1 - (i + lowBit i) < n + 1 - i := by
  have := lowBit_pos hi
  omega

/-- The portion installed by the constructor's left-to-right initialization. -/
def prefixWeights {n : ℕ} (w : Fin n → ℕ) (k : ℕ) : Fin n → ℕ :=
  fun j => if j.val < k then w j else 0

@[simp] theorem prefixWeights_zero {n : ℕ} (w : Fin n → ℕ) :
    prefixWeights w 0 = fun _ => 0 := by
  funext j
  simp [prefixWeights]

@[simp] theorem prefixWeights_length {n : ℕ} (w : Fin n → ℕ) :
    prefixWeights w n = w := by
  funext j
  simp [prefixWeights]

@[simp] theorem prefixWeights_current {n : ℕ} (w : Fin n → ℕ) (j : Fin n) :
    prefixWeights w j.val j = 0 := by simp [prefixWeights]

theorem prefixWeights_succ {n : ℕ} (w : Fin n → ℕ) (j : Fin n) :
    Function.update (prefixWeights w j.val) j (w j) = prefixWeights w (j.val + 1) := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [prefixWeights]
  · rw [Function.update_of_ne hk]
    have hne := Fin.val_ne_of_ne hk
    have heq : (k.val < j.val) = (k.val < j.val + 1) := by
      apply propext
      omega
    simp only [prefixWeights, heq]

@[simp] theorem cell_zero_weights {n : ℕ} (i : ℕ) :
    cell (fun _ : Fin n => 0) i = 0 := by simp [cell, interval]

end FenwickMath
