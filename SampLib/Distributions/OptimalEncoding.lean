module

public import Mathlib.Tactic

@[expose] public section

/-! # Cyclic binary rows, including probability one

A prefix of `A` possible words and a repeated block of length `P` encode masses
with denominator `A(P-1)`. The endpoint uses the infinite all-ones expansion;
letting the quotient carry instead would put its only bit outside the matrix.
-/

namespace SampLib.OptimalEncoding

/-- Encode the numerator, using all ones at the probability-one endpoint. -/
def blocks (A P m : ℕ) : ℕ :=
  if m = A * (P - 1) then A * P - 1 else
    (m / (P - 1)) * P + m % (P - 1)

/-- Decode a finite prefix followed by an endlessly repeated final block. -/
def decode (P E : ℕ) : ℕ := (E / P) * (P - 1) + E % P

private theorem all_ones (A P : ℕ) (hA : 0 < A) (hP : 1 < P) :
    A * P - 1 = (A - 1) * P + (P - 1) := by
  calc
    _ = (A - 1 + 1) * P - 1 := by rw [Nat.sub_add_cancel (by omega : 1 ≤ A)]
    _ = _ := by rw [add_mul, one_mul, Nat.add_sub_assoc (by omega : 1 ≤ P)]

/-- Every encoded row fits the scanned columns, including a certain row. -/
theorem blocks_lt (A P m : ℕ) (hA : 0 < A) (hP : 1 < P)
    (hm : m ≤ A * (P - 1)) : blocks A P m < A * P := by
  unfold blocks
  split_ifs with heq
  · exact Nat.sub_lt (Nat.mul_pos hA (by omega)) (by decide)
  · have hq : m / (P - 1) < A :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < P - 1)).mpr (by omega)
    have hr : m % (P - 1) < P := (Nat.mod_lt m (by omega)).trans (by omega)
    calc
      _ < (m / (P - 1)) * P + P := Nat.add_lt_add_left hr _
      _ = (m / (P - 1) + 1) * P := by ring
      _ ≤ A * P := Nat.mul_le_mul_right P (by omega)

/-- Prefix and period recover the original numerator exactly. -/
theorem decode_blocks (A P m : ℕ) (hA : 0 < A) (hP : 1 < P) :
    decode P (blocks A P m) = m := by
  unfold blocks decode
  split_ifs with heq
  · rw [all_ones A P hA hP, Nat.mul_comm (A - 1) P, Nat.mul_add_div (by omega : 0 < P),
      Nat.div_eq_of_lt (by omega : P - 1 < P), Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : P - 1 < P)]
    rw [← add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ A)]
    exact heq.symm
  · have hr : m % (P - 1) < P := (Nat.mod_lt m (by omega)).trans (by omega)
    rw [Nat.mul_comm (m / (P - 1)) P, Nat.mul_add_div (by omega : 0 < P),
      Nat.div_eq_of_lt hr, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    simpa only [Nat.mul_comm] using Nat.div_add_mod m (P - 1)

/-- The common denominator selected for a prefix followed by a cyclic block. -/
def denominator (k l : ℕ) : ℕ := 2 ^ k - 2 ^ l

/-- The repaired source's exact integer row encoder. -/
def binary (k l m : ℕ) : ℕ :=
  if m = denominator k l then 2 ^ k - 1 else
    if l = k then m else if l = 0 then m else
      (m / (2 ^ (k - l) - 1)) * 2 ^ (k - l) + m % (2 ^ (k - l) - 1)

theorem ceiling_factor {k l : ℕ} (hl : l ≤ k) :
    2 ^ l * 2 ^ (k - l) = 2 ^ k := by
  rw [← pow_add, show l + (k - l) = k by omega]

theorem denominator_factor {k l : ℕ} (hl : l ≤ k) :
    denominator k l = 2 ^ l * (2 ^ (k - l) - 1) := by
  rw [Nat.mul_sub_left_distrib, mul_one, ceiling_factor hl]
  rfl

theorem denominator_pos {k l : ℕ} (hl : l < k) : 0 < denominator k l :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) hl)

/-- On valid cyclic parameters, the optimized branches are the same block encoding. -/
theorem binary_eq_blocks {k l m : ℕ} (hl : l < k) (hm : m ≤ denominator k l) :
    binary k l m = blocks (2 ^ l) (2 ^ (k - l)) m := by
  unfold binary blocks
  rw [denominator_factor hl.le]
  by_cases he : m = 2 ^ l * (2 ^ (k - l) - 1)
  · simp only [he, ite_true, ceiling_factor hl.le]
  · rw [ite_eq_right he, ite_eq_right he, ite_eq_right (by omega : l ≠ k)]
    by_cases hz : l = 0
    · subst l
      have hm' : m ≤ 2 ^ k - 1 := by simpa [denominator] using hm
      have he' : m ≠ 2 ^ k - 1 := by simpa using he
      have hlt := lt_of_le_of_ne hm' he'
      simp [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
    · rw [ite_eq_right hz]

/-- No repaired row overflows its actual scanned width. -/
theorem binary_lt {k l m : ℕ} (hl : l < k) (hm : m ≤ denominator k l) :
    binary k l m < 2 ^ k := by
  rw [binary_eq_blocks hl hm, ← ceiling_factor hl.le]
  exact blocks_lt _ _ _ (by positivity) (one_lt_pow₀ (by decide) (by omega))
    (by rwa [← denominator_factor hl.le])

/-- Every finite prefix and repeating block has exactly its requested row mass. -/
theorem decode_binary {k l m : ℕ} (hl : l < k) (hm : m ≤ denominator k l) :
    decode (2 ^ (k - l)) (binary k l m) = m := by
  rw [binary_eq_blocks hl hm]
  exact decode_blocks _ _ _ (by positivity) (one_lt_pow₀ (by decide) (by omega))

end SampLib.OptimalEncoding
