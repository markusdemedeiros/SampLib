module

public import SampLib.Combinatorial.Laws.IntegerRange
public import Mathlib.Combinatorics.Derangements.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # The fixed-point test of a shuffled index list

A shuffled index list avoids every position exactly when its permutation is a
derangement.
-/

open Equiv
open scoped Classical

namespace SampLib.Derangement

/-- No entry equals its index, counted from `start`. -/
def avoids (xs : List ℤ) (start : ℤ) : Prop :=
  ∀ i : Fin xs.length, xs.get i ≠ start + i.val

theorem avoids_cons (x : ℤ) (xs : List ℤ) (start : ℤ) :
    avoids (x :: xs) start ↔ x ≠ start ∧ avoids xs (start + 1) := by
  simp [avoids, Fin.forall_fin_succ, add_left_comm, add_comm]

theorem avoids_cons_test (x : ℤ) (xs : List ℤ) (start : ℤ) :
    decide (avoids (x :: xs) start) =
      if x = start then false else decide (avoids xs (start + 1)) := by
  rw [avoids_cons]
  by_cases hx : x = start <;> simp [hx]

theorem interval_ofFn (lo : ℤ) (n : ℕ) :
    IntegerRange.interval lo n = List.ofFn (fun i : Fin n => lo + i.val) := by
  induction n generalizing lo with
  | zero => rfl
  | succ n IH =>
    simpa only [IntegerRange.interval, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
      Nat.cast_zero, Nat.cast_add_one, add_zero, add_left_comm, add_comm] using
      congrArg (List.cons lo) (IH (lo + 1))

theorem avoids_ofFn (n : ℕ) (σ : Perm (Fin n)) :
    avoids (List.ofFn (fun i => ((σ i).val : ℤ))) 0 ↔
      σ ∈ derangements (Fin n) := by
  constructor
  · intro h i hi
    have hindex := h ⟨i.val, by simp⟩
    apply hindex
    simpa only [List.get_eq_getElem, List.getElem_ofFn, zero_add] using
      congrArg (fun j : Fin n => (j.val : ℤ)) hi
  · intro h i hi
    let j : Fin n := ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
    apply h j
    apply Fin.ext
    apply Int.natCast_inj.mp
    simpa only [List.get_eq_getElem, List.getElem_ofFn, zero_add] using hi

end SampLib.Derangement
