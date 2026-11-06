module

public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact integer rounding to a binary significand

The exponent is unbounded. A discarded suffix selects the nearest adjacent
multiple of the quantum; a half-quantum suffix selects the even significand.
-/

namespace SampLib.BinaryRounding

theorem size_step {value : ℕ} (hv : 0 < value) :
    value.size = 1 + (value / 2).size := by
  have h := Nat.size_bit (b := value.bodd) (n := value.div2)
    (by simpa only [Nat.bit_bodd_div2] using hv.ne')
  rw [Nat.bit_bodd_div2] at h
  simpa only [Nat.div2_val, Nat.succ_eq_add_one, Nat.add_comm] using h

/-- Spacing of representable values in the input's binary binade. -/
def quantum (value precision : ℕ) : ℕ := 2 ^ (value.size - precision)

theorem quantum_pos (value precision : ℕ) : 0 < quantum value precision := by
  unfold quantum
  positivity

/-- Nearest binary value, resolving midpoint ties toward the even significand. -/
def round (value precision : ℕ) : ℕ :=
  if value.size ≤ precision then value else
    let q := quantum value precision
    let s := value / q
    let r := value % q
    if q < 2 * r ∨ (q = 2 * r ∧ s % 2 = 1) then (s + 1) * q else s * q

@[simp] theorem round_zero (precision : ℕ) : round 0 precision = 0 := by simp [round]

theorem round_exact (value precision : ℕ) (h : value.size ≤ precision) :
    round value precision = value := ite_eq_left h

/-- Midpoint rounding adds the significand's parity bit, producing an even result. -/
theorem round_tie (value precision : ℕ) (hf : precision < value.size)
    (ht : quantum value precision = 2 * (value % quantum value precision)) :
    round value precision =
      (value / quantum value precision + (value / quantum value precision) % 2) *
        quantum value precision := by
  have hnot : ¬ quantum value precision < 2 * (value % quantum value precision) := by omega
  rw [round, ite_eq_right (not_le.mpr hf)]
  dsimp only
  by_cases ho : (value / quantum value precision) % 2 = 1
  · rw [ite_eq_left (Or.inr ⟨ht, ho⟩), ho]
  · have he : (value / quantum value precision) % 2 = 0 := by omega
    have hup : ¬ (quantum value precision < 2 * (value % quantum value precision) ∨
        quantum value precision = 2 * (value % quantum value precision) ∧
          (value / quantum value precision) % 2 = 1) := by
      rintro (h | ⟨_, h⟩)
      · exact hnot h
      · exact ho h
    rw [ite_eq_right hup, he, add_zero]

theorem tie_even (value precision : ℕ) (hf : precision < value.size)
    (ht : quantum value precision = 2 * (value % quantum value precision)) :
    (round value precision / quantum value precision) % 2 = 0 := by
  rw [round_tie value precision hf ht, Nat.mul_div_cancel _ (quantum_pos value precision)]
  omega

/-- Rounding changes the value by at most half a quantum, without real-valued arithmetic. -/
theorem error_bound (value precision : ℕ) :
    2 * round value precision ≤ 2 * value + quantum value precision ∧
      2 * value ≤ 2 * round value precision + quantum value precision := by
  by_cases hf : value.size ≤ precision
  · rw [round_exact value precision hf]
    omega
  · have hq := quantum_pos value precision
    have hr := Nat.mod_lt value hq
    have hv := Nat.div_add_mod' value (quantum value precision)
    rw [round, ite_eq_right hf]
    dsimp only
    split_ifs with hup
    · have hu : quantum value precision ≤ 2 * (value % quantum value precision) := by
        rcases hup with h | ⟨h, _⟩ <;> omega
      simp only [Nat.add_mul, Nat.one_mul]
      constructor <;> omega
    · have hd : 2 * (value % quantum value precision) ≤ quantum value precision := by
        omega
      constructor <;> omega

end SampLib.BinaryRounding
