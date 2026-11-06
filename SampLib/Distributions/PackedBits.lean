module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact variable-width integer fields

A field stores its low-order digit followed by the remaining packed fields.
Division by preceding widths and reduction modulo the current width recovers
that digit, provided every field fits its allocated width.
-/

namespace SampLib.PackedBits

/-- Little-endian concatenation with a value-dependent bit width. -/
def encode (width : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | value :: values => value + 2 ^ width value * encode width values

/-- Number of bits preceding the indexed field. -/
def offset (width : ℕ → ℕ) (values : List ℕ) (i : ℕ) : ℕ :=
  ((values.take i).map width).sum

@[simp] theorem offset_zero (width : ℕ → ℕ) (values : List ℕ) : offset width values 0 = 0 := by
  simp [offset]

@[simp] theorem offset_cons_succ (width : ℕ → ℕ) (value : ℕ) (values : List ℕ) (i : ℕ) :
    offset width (value :: values) (i + 1) = width value + offset width values i := by
  simp [offset]

/-- Fitting digits never carry beyond the combined field width. -/
theorem encode_lt (width : ℕ → ℕ) (values : List ℕ)
    (hfit : ∀ value ∈ values, value < 2 ^ width value) :
    encode width values < 2 ^ offset width values values.length := by
  induction values with
  | nil => simp [encode, offset]
  | cons value values ih =>
    have hv := hfit value (by simp)
    have ht : ∀ x ∈ values, x < 2 ^ width x := fun x hx => hfit x (by simp [hx])
    rw [encode, List.length_cons, offset_cons_succ, pow_add]
    calc
      _ < 2 ^ width value + 2 ^ width value * encode width values := Nat.add_lt_add_right hv _
      _ = 2 ^ width value * (encode width values + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (ih ht))

/-- Exact decoding of every field, without a word-size or machine-integer assumption. -/
theorem decode (width : ℕ → ℕ) (values : List ℕ)
    (hfit : ∀ value ∈ values, value < 2 ^ width value) (i : ℕ) (hi : i < values.length) :
    (encode width values / 2 ^ offset width values i) % 2 ^ width values[i] = values[i] := by
  induction values generalizing i with
  | nil => simp at hi
  | cons value values ih =>
    have hv := hfit value (by simp)
    have ht : ∀ x ∈ values, x < 2 ^ width x := fun x hx => hfit x (by simp [hx])
    cases i with
    | zero =>
      simpa only [encode, offset_zero, pow_zero, Nat.div_one, List.getElem_cons_zero,
        Nat.add_mul_mod_self_left] using Nat.mod_eq_of_lt hv
    | succ i =>
      simp only [List.getElem_cons_succ, offset_cons_succ, encode, pow_add]
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hv, zero_add]
      exact ih ht i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

/-- The source's low-bit population count, limited to the requested number of positions. -/
def count : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, bits => bits % 2 + count n (bits / 2)

/-- Counting packed binary flags gives the sum of the requested prefix, including trailing zeros. -/
theorem count_encode (flags : List ℕ) (hfit : ∀ b ∈ flags, b < 2) (i : ℕ) :
    count i (encode (fun _ => 1) flags) = (flags.take i).sum := by
  induction i generalizing flags with
  | zero => simp [count]
  | succ i ih =>
    cases flags with
    | nil =>
      simpa only [encode, count, Nat.zero_mod, Nat.zero_div, zero_add,
        List.take_nil, List.sum_nil] using ih [] (by simp)
    | cons b flags =>
      have hb := hfit b (by simp)
      have ht : ∀ x ∈ flags, x < 2 := fun x hx => hfit x (by simp [hx])
      simp only [encode, pow_one, count]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
        Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, zero_add, ih flags ht]
      simp only [List.take_succ_cons, List.sum_cons]

end SampLib.PackedBits
