module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Least set bits and dyadic alignment -/

namespace FenwickMath

/-- The value of the least set bit, with the empty index assigned zero. -/
def lowBit (i : ℕ) : ℕ := if i = 0 then 0 else 2 ^ padicValNat 2 i

@[simp] theorem lowBit_zero : lowBit 0 = 0 := by simp [lowBit]

theorem lowBit_pos {i : ℕ} (hi : 0 < i) : 0 < lowBit i := by
  simp only [lowBit, ite_eq_right hi.ne']
  positivity

theorem lowBit_dvd (i : ℕ) : lowBit i ∣ i := by
  by_cases hi : i = 0
  · simp [hi]
  · simpa only [lowBit, ite_eq_right hi] using (pow_padicValNat_dvd : 2 ^ padicValNat 2 i ∣ i)

theorem lowBit_le {i : ℕ} (hi : 0 < i) : lowBit i ≤ i := Nat.le_of_dvd hi (lowBit_dvd i)

@[simp] theorem lowBit_odd (m : ℕ) : lowBit (2 * m + 1) = 1 := by
  have hodd : ¬ 2 ∣ 2 * m + 1 := by omega
  simp [lowBit, padicValNat.eq_zero_of_not_dvd hodd]

@[simp] theorem lowBit_even (m : ℕ) : lowBit (2 * m) = 2 * lowBit m := by
  by_cases hm : m = 0
  · simp [hm]
  · simp [lowBit, hm, padicValNat.mul (by decide : 2 ≠ 0) hm, pow_add]

theorem even_quotient_pos {i : ℕ} (hi : 0 < i) (he : i % 2 = 0) : 0 < i / 2 := by omega

theorem quotient_lt {i : ℕ} (hi : 0 < i) : i / 2 < i := by omega

theorem lowBit_even_quotient {i : ℕ} (he : i % 2 = 0) : lowBit i = 2 * lowBit (i / 2) := by
  simpa only [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)] using lowBit_even (i / 2)

theorem lowBit_odd_mul_pow (m a : ℕ) : lowBit ((2 * m + 1) * 2 ^ a) = 2 ^ a := by
  have hodd : ¬ 2 ∣ 2 * m + 1 := by omega
  rw [lowBit, ite_eq_right (by positivity),
    padicValNat.mul (by omega : 2 * m + 1 ≠ 0) (by positivity),
    padicValNat.eq_zero_of_not_dvd hodd, padicValNat.prime_pow, zero_add]

/-- A dyadic half-block starts at an even multiple of its length. -/
theorem lowBit_aligned {i a : ℕ} (hi : 2 ^ (a + 1) ∣ i) : lowBit (i + 2 ^ a) = 2 ^ a := by
  obtain ⟨m, rfl⟩ := hi
  have he : 2 ^ (a + 1) * m + 2 ^ a = (2 * m + 1) * 2 ^ a := by ring
  rw [he, lowBit_odd_mul_pow]

end FenwickMath
