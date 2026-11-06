module

public import SampLib.Weighted.Laws.PackedBits
public import Mathlib.Algebra.Order.BigOperators.Group.List
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The 20/32-bit categorical weight representation

A binary flag selects each field width. Counting earlier wide flags computes
the bit offset, and the generic variable-width decoder recovers the exact weight.
-/

namespace SampLib.PackedWeights

def Wide (w : ℕ) : Prop := 2 ^ 20 ≤ w

instance (w : ℕ) : Decidable (Wide w) := inferInstanceAs (Decidable (2 ^ 20 ≤ w))

def flag (w : ℕ) : ℕ := if Wide w then 1 else 0

def width (w : ℕ) : ℕ := if Wide w then 32 else 20

def flags (ws : List ℕ) : List ℕ := ws.map flag

def bits (ws : List ℕ) : ℕ := PackedBits.encode width ws

def mask (ws : List ℕ) : ℕ := PackedBits.encode (fun _ => 1) (flags ws)

def wideBefore (ws : List ℕ) (i : ℕ) : ℕ := PackedBits.count i (mask ws)

theorem flag_lt_two (w : ℕ) : flag w < 2 := by
  unfold flag
  split <;> decide

theorem flag_le_one (w : ℕ) : flag w ≤ 1 := by have := flag_lt_two w; omega

theorem flags_fit (ws : List ℕ) : ∀ b ∈ flags ws, b < 2 := by
  intro b hb
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hb
  exact flag_lt_two w

/-- The selected field width contains every permitted packed weight. -/
theorem fits_width (w : ℕ) (hw : w < 2 ^ 32) : w < 2 ^ width w := by
  by_cases h : Wide w
  · simpa only [width, ite_eq_left h] using hw
  · simpa only [width, ite_eq_right h] using (Nat.lt_of_not_ge h)

@[simp] theorem bits_cons (w : ℕ) (ws : List ℕ) :
    bits (w :: ws) = w + 2 ^ width w * bits ws := rfl

@[simp] theorem mask_cons (w : ℕ) (ws : List ℕ) :
    mask (w :: ws) = flag w + 2 * mask ws := rfl

/-- The flag prefix count is the number of earlier wide fields. -/
theorem wideBefore_eq (ws : List ℕ) (i : ℕ) :
    wideBefore ws i = ((ws.take i).map flag).sum := by
  rw [wideBefore, mask, PackedBits.count_encode _ (flags_fit ws)]
  simp only [flags, List.map_take]

theorem wideBefore_le (ws : List ℕ) (i : ℕ) : wideBefore ws i ≤ i := by
  rw [wideBefore_eq]
  have h := List.sum_le_length_nsmul ((ws.take i).map flag) 1
    (by simpa only [List.forall_mem_map] using fun w (_ : w ∈ ws.take i) => flag_le_one w)
  simp only [List.length_map, nsmul_eq_mul, Nat.cast_id, mul_one] at h
  exact h.trans (by simp only [List.length_take]; exact Nat.min_le_left _ _)

private theorem width_sum (ws : List ℕ) :
    (ws.map width).sum = 20 * ws.length + 12 * (ws.map flag).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw : width w = 20 + 12 * flag w := by
      by_cases h : Wide w <;> simp [width, flag, h]
    simp only [List.map_cons, List.sum_cons, List.length_cons, hw, ih]
    ring

/-- The source's population-count formula is the exact variable-width offset. -/
theorem offset_eq (ws : List ℕ) (i : ℕ) (hi : i ≤ ws.length) :
    PackedBits.offset width ws i = 32 * wideBefore ws i + 20 * (i - wideBefore ws i) := by
  rw [PackedBits.offset, width_sum, List.length_take, Nat.min_eq_left hi, ← wideBefore_eq]
  have := wideBefore_le ws i
  omega

/-- Every individual width flag survives binary packing. -/
theorem mask_bit (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    mask ws / 2 ^ i % 2 = flag ws[i] := by
  have h := PackedBits.decode (fun _ => 1) (flags ws) (by
    simpa only [pow_one] using flags_fit ws) i (by simpa only [flags, List.length_map] using hi)
  simpa [mask, flags, PackedBits.offset, Function.comp_def, List.map_const',
    Nat.min_eq_left hi.le] using h

/-- The source's flag comparison selects precisely the corresponding field width. -/
theorem decoded_width (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    (if mask ws / 2 ^ i % 2 = 1 then 32 else 20) = width ws[i] := by
  rw [mask_bit ws i hi]
  by_cases h : Wide ws[i] <;> simp [flag, width, h]

/-- Exact unpacking, including zero weights and mixed short/wide fields. -/
theorem decode (ws : List ℕ) (hfit : ∀ w ∈ ws, w < 2 ^ 32) (i : ℕ) (hi : i < ws.length) :
    bits ws / 2 ^ (32 * wideBefore ws i + 20 * (i - wideBefore ws i)) %
      2 ^ (if mask ws / 2 ^ i % 2 = 1 then 32 else 20) = ws[i] := by
  rw [← offset_eq ws i hi.le, decoded_width ws i hi]
  exact PackedBits.decode width ws (fun w hw => fits_width w (hfit w hw)) i hi

/-- Appending the next field agrees with the source's accumulator update. -/
theorem bits_accumulator (w : ℕ) (ws : List ℕ) (offset accumulator : ℕ) :
    accumulator + 2 ^ offset * bits (w :: ws) =
      (accumulator + w * 2 ^ offset) + 2 ^ (offset + width w) * bits ws := by
  rw [bits_cons, pow_add]
  ring

theorem mask_accumulator (w : ℕ) (ws : List ℕ) (index accumulator : ℕ) :
    accumulator + 2 ^ index * mask (w :: ws) =
      (accumulator + flag w * 2 ^ index) + 2 ^ (index + 1) * mask ws := by
  rw [mask_cons, pow_succ]
  ring

end SampLib.PackedWeights
