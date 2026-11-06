module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-! # Reverse binomial kernels

Conditioning a split binomial count on its total gives hypergeometric weights.
Vandermonde supplies normalization; pointwise factorization avoids dividing by
`p` or `1-p`, including deterministic endpoint biases.
-/

open MeasureTheory Finset Finset.Nat
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ReverseBinomial

noncomputable section

/-- Impossible histories have zero numerator, including `j>k`. -/
def numerator (n m k j : ℕ) : ℕ :=
  if j ≤ k ∧ j ≤ n then n.choose j * (m - n).choose (k - j) else 0

/-- The exact rational conditional coefficient used by envelope callbacks. -/
def coefficient (n m k j : ℕ) : ℚ := (numerator n m k j : ℚ) / m.choose k

/-- The same coefficient acting on arbitrary nonnegative extended-real credits. -/
def weight (n m k j : ℕ) : ℝ≥0∞ := ofReal (coefficient n m k j : ℝ)

theorem numerator_of_le (n m k j : ℕ) (hj : j ≤ k) :
    numerator n m k j = n.choose j * (m - n).choose (k - j) := by
  by_cases hn : j ≤ n
  · simp only [numerator, and_self_iff, hj, hn, ite_true]
  · simp [numerator, hn, Nat.choose_eq_zero_of_lt (by omega : n < j)]

theorem numerator_sum (n m k : ℕ) (hnm : n ≤ m) :
    ∑ j ∈ range (k + 1), numerator n m k j = m.choose k := by
  have h := Nat.add_choose_eq n (m - n) k
  rw [Nat.add_sub_of_le hnm, sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [h]
  exact sum_congr rfl (fun j hj => numerator_of_le n m k j (by simpa using hj))

/-- Source-style formula: a negative remainder contributes zero. -/
theorem coefficient_eq (n m k j : ℕ) :
    coefficient n m k j = (n.choose j : ℚ) *
      (if j ≤ k then ((m - n).choose (k - j) : ℚ) else 0) / m.choose k := by
  by_cases hj : j ≤ k
  · simp only [coefficient, numerator_of_le n m k j hj, Nat.cast_mul, ite_eq_left hj]
  · simp [coefficient, numerator, hj]

theorem coefficient_zero_of_lt_total (n m k j : ℕ) (hj : k < j) :
    coefficient n m k j = 0 := by simp [coefficient, numerator, not_le.mpr hj]

theorem coefficient_zero_of_lt_degree (n m k j : ℕ) (hj : n < j) :
    coefficient n m k j = 0 := by simp [coefficient, numerator, not_le.mpr hj]

theorem coefficient_nonneg (n m k j : ℕ) : 0 ≤ coefficient n m k j := by
  unfold coefficient
  positivity

theorem coefficient_sum (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ range (k + 1), coefficient n m k j = 1 := by
  simp only [coefficient, ← sum_div]
  rw [← Nat.cast_sum, numerator_sum n m k hnm]
  exact div_self (by exact_mod_cast (Nat.choose_pos hkm).ne')

/-- Summing over possible previous heads gives the same normalization. -/
theorem coefficient_sum_degree (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ range (n + 1), coefficient n m k j = 1 := by
  rw [← coefficient_sum n m k hnm hkm]
  rcases le_total n k with h | h
  · apply sum_subset (range_mono (Nat.add_le_add_right h 1))
    intro j _ hj
    exact coefficient_zero_of_lt_degree n m k j (by simpa using hj)
  · symm
    apply sum_subset (range_mono (Nat.add_le_add_right h 1))
    intro j _ hj
    exact coefficient_zero_of_lt_total n m k j (by simpa using hj)

theorem coefficient_sum_real (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ range (k + 1), (coefficient n m k j : ℝ) = 1 := by
  exact_mod_cast coefficient_sum n m k hnm hkm

theorem coefficient_sum_degree_real (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ range (n + 1), (coefficient n m k j : ℝ) = 1 := by
  exact_mod_cast coefficient_sum_degree n m k hnm hkm

theorem coefficient_le_one (n m k j : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    coefficient n m k j ≤ 1 := by
  by_cases hj : j ≤ k
  · rw [← coefficient_sum n m k hnm hkm]
    exact single_le_sum (fun a _ => coefficient_nonneg n m k a) (mem_range.mpr (by omega))
  · rw [coefficient_zero_of_lt_total n m k j (by omega)]
    exact zero_le_one

theorem weight_coefficient (n m k j : ℕ) :
    weight n m k j = ofReal (coefficient n m k j : ℝ) := rfl

theorem weight_eq_div (n m k j : ℕ) (hkm : k ≤ m) :
    weight n m k j = (numerator n m k j : ℝ≥0∞) / m.choose k := by
  simp only [weight, coefficient, Rat.cast_div, Rat.cast_natCast]
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.choose_pos hkm),
    ENNReal.ofReal_natCast]
  norm_cast

theorem weight_sum (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    ∑ j ∈ range (k + 1), weight n m k j = 1 := by
  simp_rw [weight_eq_div n m k _ hkm]
  rw [← ENNReal.sum_div, ← Nat.cast_sum, numerator_sum n m k hnm]
  exact ENNReal.div_self (by exact_mod_cast (Nat.choose_pos hkm).ne') (by simp)

theorem weight_eq_zero_of_lt (n m k j : ℕ) (hkj : k < j) : weight n m k j = 0 := by
  simp [weight, coefficient_zero_of_lt_total n m k j hkj]

theorem coefficient_pos (n m k j : ℕ) (hkm : k ≤ m) (hjk : j ≤ k) (hjn : j ≤ n)
    (hrest : k - j ≤ m - n) : 0 < coefficient n m k j := by
  rw [coefficient, numerator, ite_eq_left ⟨hjk, hjn⟩]
  exact div_pos (by exact_mod_cast mul_pos (Nat.choose_pos hjn) (Nat.choose_pos hrest))
    (by exact_mod_cast Nat.choose_pos hkm)

theorem weight_pos (n m k j : ℕ) (hkm : k ≤ m) (hjk : j ≤ k) (hjn : j ≤ n)
    (hrest : k - j ≤ m - n) : 0 < weight n m k j := by
  rw [weight_coefficient, ENNReal.ofReal_pos]
  exact_mod_cast coefficient_pos n m k j hkm hjk hjn hrest

/-- Raw conditional measure, defined also at totals outside the binomial support. -/
def kernel (n m k : ℕ) : Measure ℕ :=
  ∑ j ∈ range (k + 1), weight n m k j • Measure.dirac j

/-- A valid-total conditional law. The proof arguments provide its probability instance. -/
abbrev law (n m k : ℕ) (_hnm : n ≤ m) (_hkm : k ≤ m) : Measure ℕ := kernel n m k

theorem kernel_singleton (n m k j : ℕ) : kernel n m k {j} = weight n m k j := by
  rw [kernel, Measure.finsetSum_apply]
  by_cases hj : j ≤ k
  · rw [sum_eq_single j]
    · simp
    · intro a _ ha
      simp [ha]
    · simp [mem_range, hj]
  · rw [sum_eq_zero]
    · exact (weight_eq_zero_of_lt n m k j (by omega)).symm
    · intro a ha
      have hne : j ≠ a := by simp only [mem_range] at ha; omega
      simp [hne]

instance (n m k : ℕ) (hnm : n ≤ m) (hkm : k ≤ m) :
    IsProbabilityMeasure (law n m k hnm hkm) where
  measure_univ := by simpa [law, kernel] using weight_sum n m k hnm hkm

theorem expectation (n m k : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ j, F j ∂kernel n m k = ∑ j ∈ range (k + 1), weight n m k j * F j := by
  simp [kernel, lintegral_finsetSum_measure]

/-- Before any trials have been exposed, the previous count is deterministically zero. -/
theorem coefficient_zero_degree (m k j : ℕ) (hkm : k ≤ m) :
    coefficient 0 m k j = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst j
    simp only [coefficient, numerator, zero_le, and_self, ite_true, Nat.choose_zero_right,
      Nat.sub_zero, one_mul]
    rw [div_self (by exact_mod_cast (Nat.choose_pos hkm).ne')]
  · simp [coefficient, numerator, hj]

theorem kernel_zero_left (m k : ℕ) (hkm : k ≤ m) : kernel 0 m k = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro j
  rw [kernel_singleton, weight_coefficient, coefficient_zero_degree m k j hkm]
  by_cases hj : j = 0 <;> simp [hj]

end

end SampLib.ReverseBinomial
