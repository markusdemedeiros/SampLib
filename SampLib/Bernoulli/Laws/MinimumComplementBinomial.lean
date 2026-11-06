module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

@[expose] public section

/-! # The conditional binomial stage of the minimum-complement factory

The binomial coefficient in the source acceptance ratio cancels its sampling
mass. Factoring off `p^m(1-p)^m` leaves one complete binomial expansion.
-/

open Finset

namespace SampLib.MinimumComplement

noncomputable section

/-- The raw source ratio; admissibility depends on the chosen padding `r`. -/
def acceptance (m r j : ℕ) : ℝ :=
  if m ≤ j ∧ j ≤ m + r then
    (4 ^ m * r.choose (j - m) : ℕ) / (2 * ((2 * m + r).choose j : ℝ))
  else 0

private def weight (p : ℝ) (n j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

private theorem weight_sum (p : ℝ) (r : ℕ) :
    ∑ j ∈ range (r + 1), weight p r j = 1 := by
  have h := (add_pow p (1 - p) r).symm
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  simpa only [weight, mul_comm, mul_left_comm, mul_assoc] using h

private theorem weighted_term (p : ℝ) (m r j : ℕ) (hj : j ≤ r) :
    weight p (2 * m + r) (m + j) * acceptance m r (m + j) =
      (4 * p * (1 - p)) ^ m / 2 * weight p r j := by
  have hband : m ≤ m + j ∧ m + j ≤ m + r := ⟨by omega, by omega⟩
  have hc : (((2 * m + r).choose (m + j) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m + j ≤ 2 * m + r)).ne'
  rw [acceptance, ite_eq_left hband, Nat.add_sub_cancel_left]
  simp only [weight, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 2 * m + r - (m + j) = m + (r - j) by omega, pow_add, pow_add, mul_pow, mul_pow]
  field_simp

/-- The conditional success probability is `(4p(1-p))^m/2`, independently of padding. -/
theorem binomial_mean (p : ℝ) (m r : ℕ) :
    (∑ j ∈ range (2 * m + r + 1),
      ((2 * m + r).choose j : ℝ) * p ^ j * (1 - p) ^ (2 * m + r - j) *
        acceptance m r j) = (4 * p * (1 - p)) ^ m / 2 := by
  change (∑ j ∈ range (2 * m + r + 1), weight p (2 * m + r) j * acceptance m r j) = _
  have hrestrict :
      (∑ j ∈ range (2 * m + r + 1), weight p (2 * m + r) j * acceptance m r j) =
        ∑ j ∈ Ico m (m + r + 1), weight p (2 * m + r) j * acceptance m r j := by
    symm
    apply sum_subset
    · intro j hj
      simp only [mem_Ico, mem_range] at hj ⊢
      omega
    · intro j hj hnot
      have hband : ¬(m ≤ j ∧ j ≤ m + r) := by
        simp only [mem_Ico, not_and] at hnot
        omega
      simp only [acceptance, ite_eq_right hband, mul_zero]
  rw [hrestrict, sum_Ico_eq_sum_range]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  calc
    _ = ∑ j ∈ range (r + 1), (4 * p * (1 - p)) ^ m / 2 * weight p r j := by
      apply sum_congr rfl
      intro j hj
      exact weighted_term p m r j (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = _ := by rw [← mul_sum, weight_sum, mul_one]

end

end SampLib.MinimumComplement
