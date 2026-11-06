import SampLib.Uniform.Laws.UniformInt

/-! # Credit for uniform words built from fair bits

After reading `n` bits, a prefix `v` is followed by a uniform suffix of width `2^n`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.RandomBits

noncomputable section

/-- Expected continuation credit for a fixed prefix and a uniform binary suffix. -/
def credit (n v : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ k ∈ range (2 ^ n), F (v * 2 ^ n + k)) / 2 ^ n

@[simp] theorem credit_zero (v : ℕ) (F : ℕ → ℝ≥0∞) : credit 0 v F = F v := by
  simp [credit]

/-- The next fair bit partitions the suffix interval into its two equal halves. -/
theorem expectation (n v : ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ b ∈ range 2, credit n (v * 2 + b) F) / 2 = credit (n + 1) v F := by
  have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
  have hleft (k : ℕ) : (v * 2) * 2 ^ n + k = v * 2 ^ (n + 1) + k := by
    rw [pow_succ]; ring
  have hright (k : ℕ) : (v * 2 + 1) * 2 ^ n + k =
      v * 2 ^ (n + 1) + (2 ^ n + k) := by rw [pow_succ]; ring
  simp only [sum_range_succ, sum_range_zero, zero_add, add_zero, credit]
  simp_rw [hleft, hright]
  rw [hp, sum_range_add]
  simp only [ENNReal.div_eq_inv_mul]
  rw [pow_succ, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
  ring

end

end SampLib.RandomBits
