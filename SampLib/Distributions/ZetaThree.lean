import SampLib.Distributions.PositiveSeries
import SampLib.Distributions.ZetaThreeMathlib

/-! # A reciprocal-cube coin

The inverse-square telescoping majorant gives the exact remainder certificate
used by Occil's getter. The target is the ordinary convergent series for ζ(3).
-/

open Finset

namespace SampLib.ZetaThree

noncomputable section

def term (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 3

def zetaThree : ℝ := ∑' n, term n

theorem summable_term : Summable term := by
  have h := (Real.summable_nat_pow_inv (p := 3)).mpr (by norm_num)
  change Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3)
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using (summable_nat_add_iff 1).mpr h

/-- The tail majorant is the discrete derivative of an inverse square. -/
theorem term_le_difference (n : ℕ) (hn : 1 ≤ n) :
    term n ≤ 1 / (2 * (n : ℝ) ^ 2) - 1 / (2 * ((n : ℝ) + 1) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold term
  have hpos : (0 : ℝ) < n := by positivity
  apply (le_sub_iff_add_le).mpr
  field_simp
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem tail_le (k : ℕ) (hk : 1 ≤ k) :
    (∑' n, term (n + k)) ≤ 1 / (2 * (k : ℝ) ^ 2) := by
  apply Real.tsum_le_of_sum_range_le (fun n => by unfold term; positivity)
  intro N
  have h : (∑ n ∈ range N, term (n + k)) ≤
      1 / (2 * (k : ℝ) ^ 2) - 1 / (2 * ((N + k : ℕ) : ℝ) ^ 2) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have ht := term_le_difference (N + k) (by omega)
      push_cast at ih ht ⊢
      convert (add_le_add ih ht) using 1; ring
  exact h.trans (sub_le_self _ (by positivity))

theorem zetaThree_le : zetaThree ≤ 5 / 4 := by
  have h := tail_le 2 (by omega)
  have he := summable_term.sum_add_tsum_nat_add 2
  have hf : (∑ i ∈ range 2, term i) = 9 / 8 := by norm_num [sum_range_succ, term]
  rw [hf] at he
  norm_num at h
  unfold zetaThree
  linarith

def coefficient (n : ℕ) : FromPositiveSeries.Coefficient where
  numerator := 3
  denominator := 4 * (n + 1) * (n + 1) * (n + 1)
  positive := by positivity
  errorNumerator := 3
  errorDenominator := 8 * (n + 1) * (n + 1)
  errorPositive := by positivity

theorem coefficient_value (n : ℕ) : (coefficient n).value = 3 / 4 * term n := by
  simp only [coefficient, FromPositiveSeries.Coefficient.value, term,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp

theorem coefficient_error (n : ℕ) :
    (coefficient n).error = 3 / (8 * ((n : ℝ) + 1) ^ 2) := by
  simp [coefficient, FromPositiveSeries.Coefficient.error]
  ring

def parameters : FromPositiveSeries.Parameters where
  coefficient := coefficient
  summable := by simpa only [coefficient_value] using summable_term.mul_left (3 / 4)
  mass_le_one := by
    simp only [coefficient_value, tsum_mul_left]
    have hz := zetaThree_le
    unfold zetaThree at hz
    linarith
  remainder n := by
    simp only [coefficient_value, coefficient_error, tsum_mul_left, ← mul_sum]
    have he := summable_term.sum_add_tsum_nat_add (n + 1)
    have ht := tail_le (n + 1) (by omega)
    push_cast at ht
    have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hr : (3 : ℝ) / 4 * (1 / (2 * ((n : ℝ) + 1) ^ 2)) =
        3 / (8 * ((n : ℝ) + 1) ^ 2) := by
      field_simp
      norm_num
    rw [hr] at hm
    linarith
  tight ε hε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (3 / (8 * ε))
    refine ⟨n, ?_⟩
    rw [coefficient_error]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1) ^ 2)).mpr
    have hn' : 3 < (n : ℝ) * (8 * ε) := (div_lt_iff₀ (by positivity)).mp hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg (n : ℝ)]

theorem bias_coe : (FromPositiveSeries.bias parameters : ℝ) = 3 / 4 * zetaThree := by
  simp [FromPositiveSeries.bias, parameters, coefficient_value, zetaThree, tsum_mul_left]

end

end SampLib.ZetaThree
