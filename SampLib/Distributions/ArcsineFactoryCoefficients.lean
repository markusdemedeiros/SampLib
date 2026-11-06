module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # The interleaved central-binomial coefficients of the arcsine factory

Adjacent terms share either a central-binomial weight or an odd denominator.
This makes their monotonicity transparent and bounds them by a reciprocal.
-/

open Filter
open scoped Topology

namespace SampLib.ArcsineFactoryCoefficients

noncomputable section

def weight (n : ℕ) : ℚ := n.centralBinom / (4 : ℚ) ^ n

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem weight_le_one (n : ℕ) : weight n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℚ) < 4 ^ n)).mpr
  exact_mod_cast Nat.centralBinom_le_four_pow n

private theorem central_succ_le (n : ℕ) :
    ((n + 1).centralBinom : ℚ) ≤ 4 * n.centralBinom := by
  have h : ((n : ℚ) + 1) * (n + 1).centralBinom =
      2 * (2 * n + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℚ) < (n : ℚ) + 1)).mp
  nlinarith [h, Nat.cast_nonneg (α := ℚ) n.centralBinom]

theorem weight_succ (n : ℕ) :
    weight (n + 1) = weight n * (1 - (1 / 2 : ℚ) / (n + 1)) := by
  have h : ((n : ℚ) + 1) * (n + 1).centralBinom =
      2 * (2 * n + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold weight
  rw [pow_succ]
  field_simp
  nlinarith [h]

theorem weight_succ_le (n : ℕ) : weight (n + 1) ≤ weight n := by
  unfold weight
  rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (4 * (n.centralBinom : ℚ)) * 4 ^ n :=
      mul_le_mul_of_nonneg_right (central_succ_le n) (by positivity)
    _ = _ := by ring

def coefficient (n : ℕ) : ℚ :=
  if n % 2 = 0 then weight (n / 2) / (n + 1) else weight (n / 2 + 1) / n

@[simp] theorem coefficient_even (k : ℕ) :
    coefficient (2 * k) = weight k / (2 * k + 1) := by
  simp [coefficient]

@[simp] theorem coefficient_odd (k : ℕ) :
    coefficient (2 * k + 1) = weight (k + 1) / (2 * k + 1) := by
  have h : (2 * k + 1) / 2 = k := by omega
  simp [coefficient, h]

@[simp] theorem coefficient_zero : coefficient 0 = 1 := by simp [coefficient, weight]

theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  unfold coefficient
  split_ifs <;> exact div_nonneg (weight_nonneg _) (by positivity)

theorem coefficient_antitone : Antitone coefficient := by
  apply antitone_nat_of_succ_le
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have he : n = 2 * (n / 2) := by omega
    rw [he, coefficient_even, coefficient_odd]
    exact div_le_div_of_nonneg_right (weight_succ_le _) (by positivity)
  · have ho : n = 2 * (n / 2) + 1 := by omega
    rw [ho, show 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) by omega,
      coefficient_even, coefficient_odd]
    apply div_le_div_of_nonneg_left (weight_nonneg _) (by positivity)
    push_cast
    linarith

/-- The reciprocal bound suffices for the sequential alternating-series endpoint. -/
theorem coefficient_bound (n : ℕ) : coefficient n ≤ 2 / ((n : ℚ) + 1) := by
  unfold coefficient
  split_ifs with hn
  · calc
      _ ≤ 1 / ((n : ℚ) + 1) :=
        div_le_div_of_nonneg_right (weight_le_one _) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · have hn0 : 0 < n := by omega
    calc
      _ ≤ 1 / (n : ℚ) :=
        div_le_div_of_nonneg_right (weight_le_one _) (by positivity)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have : (1 : ℚ) ≤ n := by exact_mod_cast hn0
        nlinarith

theorem coefficient_vanishes :
    Tendsto (fun n => (coefficient n : ℝ)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (coefficient n : ℝ) ≤ 2 / ((n : ℝ) + 1) := by
    have h : (coefficient n : ℝ) ≤ ((2 / ((n : ℚ) + 1) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr (coefficient_bound n)
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using h
  apply squeeze_zero (fun n => by exact_mod_cast coefficient_nonneg n) hbound
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

end

end SampLib.ArcsineFactoryCoefficients
