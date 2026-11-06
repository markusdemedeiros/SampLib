module

public import Metrology.ProbLang.Measure
public import Mathlib.Logic.Encodable.Pi

@[expose] public section

/-! # Backward expectations for finite reservoir scans

At stream index n, a ticket in 0,...,n replaces that slot when it is below the
reservoir capacity. Otherwise the slots are retained.
-/

open scoped ENNReal Classical

namespace SampLib.ReservoirLaw

noncomputable section

abbrev Slots (k : ℕ) := Fin k → ℕ

instance (k : ℕ) : MeasurableSpace (Slots k) := ⊤
instance (k : ℕ) : MeasurableSingletonClass (Slots k) := ⟨fun _ => trivial⟩

/-- Apply one reservoir ticket to the current slot contents. -/
def advance {k : ℕ} (start : ℕ) (s : Slots k) (j : Fin (start + 1)) : Slots k :=
  if h : j.val < k then Function.update s ⟨j.val, h⟩ start else s

@[simp] theorem advance_of_lt {k start : ℕ} (s : Slots k) (j : Fin (start + 1))
    (h : j.val < k) : advance start s j = Function.update s ⟨j.val, h⟩ start := dite_eq_left h

@[simp] theorem advance_of_le {k start : ℕ} (s : Slots k) (j : Fin (start + 1))
    (h : k ≤ j.val) : advance start s j = s := dite_eq_right (by omega)

theorem advance_lt {k start : ℕ} (s : Slots k) (j : Fin (start + 1))
    (h : j.val < k) : advance start s j = Function.update s ⟨j.val, h⟩ start :=
  advance_of_lt s j h

theorem advance_ge {k start : ℕ} (s : Slots k) (j : Fin (start + 1))
    (h : k ≤ j.val) : advance start s j = s := advance_of_le s j h

/-- Expected terminal credit after the remaining finite scan. -/
def finish {k : ℕ} : ℕ → ℕ → Slots k → (Slots k → ℝ≥0∞) → ℝ≥0∞
  | _, 0, s, F => F s
  | start, steps + 1, s, F =>
      (∑ j : Fin (start + 1), finish (start + 1) steps (advance start s j) F) /
        (start + 1 : ℕ)

@[simp] theorem finish_zero {k : ℕ} (start : ℕ) (s : Slots k) (F : Slots k → ℝ≥0∞) :
    finish start 0 s F = F s := rfl

theorem finish_step {k : ℕ} (start steps : ℕ) (s : Slots k) (F : Slots k → ℝ≥0∞) :
    finish start (steps + 1) s F =
      (∑ j : Fin (start + 1), finish (start + 1) steps (advance start s j) F) /
        (start + 1 : ℕ) := rfl

@[simp] theorem finish_one {k : ℕ} (start : ℕ) (s : Slots k) (F : Slots k → ℝ≥0∞) :
    finish start 1 s F =
      (∑ j : Fin (start + 1), F (advance start s j)) / (start + 1 : ℕ) := rfl

@[simp] theorem finish_const {k : ℕ} (start steps : ℕ) (s : Slots k) (c : ℝ≥0∞) :
    finish start steps s (fun _ => c) = c := by
  induction steps generalizing start s with
  | zero => rfl
  | succ steps ih =>
    simp only [finish_step, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]

/-- Splitting the remaining stream composes the corresponding expectation operators. -/
theorem finish_append {k : ℕ} (start a b : ℕ) (s : Slots k) (F : Slots k → ℝ≥0∞) :
    finish start (a + b) s F =
      finish start a s (fun t => finish (start + a) b t F) := by
  induction a generalizing start s with
  | zero => simp
  | succ a ih =>
    simp only [Nat.succ_add, finish_step, ih]
    simp only [Nat.add_succ]

end

end SampLib.ReservoirLaw

