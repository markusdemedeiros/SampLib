module

public import SampLib.Constants.Laws.RealContinuedFraction
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # Euler's simple continued fraction

Positive integrals of `xⁿ (1-x)ᵐ exp x` supply the Euclidean remainders of
`[2; 1, 2, 1, 1, 4, …]`. Their three-term recurrence identifies the fraction
by uniqueness, without a separate convergence argument for its convergents.
-/

open Set MeasureTheory

namespace SampLib.EulerContinuedFraction

noncomputable section

/-- The simple coefficients after the initial integer part of `exp 1`. -/
def partialQuotient (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i % 3 = 0 then 2 * (i / 3) else 1

theorem one_le_partialQuotient (i : ℕ) : 1 ≤ partialQuotient i := by
  unfold partialQuotient
  split_ifs with hzero hdiv
  · rfl
  · have : 1 ≤ i / 3 := by omega
    omega
  · rfl

/-- Replacing the first denominator gives `1 / (c + exp 1 - 2)`. -/
def coefficient (c : ℝ) (hc : 1 ≤ c) (i : ℕ) : RealContinuedFraction.Coefficient where
  numerator := 1
  denominator := if i = 1 then c else partialQuotient i
  positive := zero_lt_one
  lower := by split_ifs <;> first | exact hc | exact_mod_cast one_le_partialQuotient i
  bounded := by split_ifs <;> first | exact hc | exact_mod_cast one_le_partialQuotient i
  last := false

private def kernel (n m : ℕ) (x : ℝ) : ℝ := x ^ n * (1 - x) ^ m * Real.exp x

private def integral (n m : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, kernel n m x

private theorem kernel_continuous (n m : ℕ) : Continuous (kernel n m) := by
  unfold kernel
  fun_prop

private theorem kernel_integrable (n m : ℕ) :
    IntervalIntegrable (kernel n m) volume 0 1 := (kernel_continuous n m).intervalIntegrable _ _

private theorem integral_pos (n m : ℕ) : 0 < integral n m := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (kernel_integrable n m) _ zero_lt_one
  intro x hx
  unfold kernel
  exact mul_pos (mul_pos (pow_pos hx.1 _) (pow_pos (sub_pos.mpr hx.2) _)) (Real.exp_pos x)

private theorem integral_split (n m : ℕ) :
    integral n m = integral (n + 1) m + integral n (m + 1) := by
  unfold integral
  rw [← intervalIntegral.integral_add (kernel_integrable (n + 1) m)
    (kernel_integrable n (m + 1))]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [kernel, pow_succ]
  ring

/-- Integrating the derivative of a polynomial times the exponential removes its boundary terms. -/
private theorem integral_recurrence (n m : ℕ) :
    (n + 1 : ℝ) * integral n (m + 1) - (m + 1 : ℝ) * integral (n + 1) m +
      integral (n + 1) (m + 1) = 0 := by
  have hderiv (x : ℝ) :
      HasDerivAt (kernel (n + 1) (m + 1))
        ((n + 1 : ℝ) * kernel n (m + 1) x -
          (m + 1 : ℝ) * kernel (n + 1) m x + kernel (n + 1) (m + 1) x) x := by
    apply ((((hasDerivAt_id x).fun_pow (n + 1)).fun_mul
      (((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)).fun_pow (m + 1))).fun_mul
        (Real.hasDerivAt_exp x)).congr_deriv
    simp [kernel, pow_succ]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    ((((kernel_integrable n (m + 1)).const_mul (n + 1 : ℝ)).sub
      ((kernel_integrable (n + 1) m).const_mul (m + 1 : ℝ))).add
        (kernel_integrable (n + 1) (m + 1)))
  rw [intervalIntegral.integral_add
      (((kernel_integrable n (m + 1)).const_mul (n + 1 : ℝ)).sub
        ((kernel_integrable (n + 1) m).const_mul (m + 1 : ℝ)))
      (kernel_integrable (n + 1) (m + 1)),
    intervalIntegral.integral_sub ((kernel_integrable n (m + 1)).const_mul (n + 1 : ℝ))
      ((kernel_integrable (n + 1) m).const_mul (m + 1 : ℝ)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa [integral, kernel] using h

private theorem integral_diagonal (n : ℕ) :
    (n + 1 : ℝ) * integral (n + 1) n =
      (n + 1 : ℝ) * integral n (n + 1) + integral (n + 1) (n + 1) := by
  linarith [integral_recurrence n n]

private theorem integral_off_diagonal (n : ℕ) :
    (n + 1 : ℝ) * integral n (n + 1) =
      2 * (n + 1 : ℝ) * integral (n + 1) (n + 1) + integral (n + 2) (n + 1) := by
  have h := integral_recurrence n (n + 1)
  have hleft := integral_split n (n + 1)
  have hright := integral_split (n + 1) (n + 1)
  push_cast at h
  linear_combination (n + 1 : ℝ) * hleft + hright + h

private theorem integral_one_zero : integral 1 0 = 1 := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun x => (x - 1) * Real.exp x) (kernel 1 0 x) x := by
    apply (((hasDerivAt_id x).sub_const 1).fun_mul (Real.hasDerivAt_exp x)).congr_deriv
    simp [kernel]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (kernel_integrable 1 0)
  simpa [integral] using h

private theorem integral_zero_one : integral 0 1 = Real.exp 1 - 2 := by
  have h := integral_split 0 0
  have he : integral 0 0 = Real.exp 1 - 1 := by
    simp [integral, kernel, integral_exp]
  rw [integral_one_zero, he] at h
  linarith

/-- Successive positive remainders of the Euclidean algorithm for `exp 1 - 2`. -/
private def remainder (j : ℕ) : ℝ :=
  let n := j / 3
  if j % 3 = 0 then integral (n + 1) n / n.factorial
  else if j % 3 = 1 then integral n (n + 1) / n.factorial
  else integral (n + 1) (n + 1) / (n + 1).factorial

private theorem remainder_pos (j : ℕ) : 0 < remainder j := by
  unfold remainder
  split_ifs <;> apply div_pos (integral_pos _ _) <;>
    exact_mod_cast Nat.factorial_pos _

private theorem remainder_zero : remainder 0 = 1 := by
  simp [remainder, integral_one_zero]

private theorem remainder_one : remainder 1 = Real.exp 1 - 2 := by
  simp [remainder, integral_zero_one]

private theorem remainder_block_zero (n : ℕ) :
    remainder (3 * n) = integral (n + 1) n / n.factorial := by
  simp [remainder]

private theorem remainder_block_one (n : ℕ) :
    remainder (3 * n + 1) = integral n (n + 1) / n.factorial := by
  simp [remainder, Nat.add_div, Nat.add_mod]

private theorem remainder_block_two (n : ℕ) :
    remainder (3 * n + 2) = integral (n + 1) (n + 1) / (n + 1).factorial := by
  simp [remainder, Nat.add_div, Nat.add_mod]

private theorem partialQuotient_block_two (n : ℕ) : partialQuotient (3 * n + 2) = 1 := by
  simp [partialQuotient, Nat.add_mod]

private theorem partialQuotient_block_three (n : ℕ) :
    partialQuotient (3 * n + 3) = 2 * (n + 1) := by
  simp [partialQuotient]

private theorem partialQuotient_block_four (n : ℕ) : partialQuotient (3 * n + 4) = 1 := by
  simp [partialQuotient, Nat.add_mod]

/-- Each positive remainder divides its predecessor with the prescribed quotient. -/
private theorem remainder_recurrence (j : ℕ) :
    remainder j = (partialQuotient (j + 2) : ℝ) * remainder (j + 1) + remainder (j + 2) := by
  obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, j = 3 * n ∨ j = 3 * n + 1 ∨ j = 3 * n + 2 := by
    refine ⟨j / 3, ?_⟩
    omega
  · rw [partialQuotient_block_two, Nat.cast_one, one_mul,
      remainder_block_zero, remainder_block_one, remainder_block_two]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply (div_eq_iff hf).mpr
    field_simp [hf, hn]
    nlinarith [integral_diagonal n]
  · rw [show 3 * n + 1 + 2 = 3 * n + 3 by omega,
      show 3 * n + 1 + 1 = 3 * n + 2 by omega,
      partialQuotient_block_three, remainder_block_one, remainder_block_two,
      show 3 * n + 3 = 3 * (n + 1) by omega, remainder_block_zero]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply (div_eq_iff hf).mpr
    field_simp [hf, hn]
    nlinarith [integral_off_diagonal n]
  · rw [show 3 * n + 2 + 2 = 3 * n + 4 by omega,
      show 3 * n + 2 + 1 = 3 * (n + 1) by omega,
      partialQuotient_block_four, Nat.cast_one, one_mul,
      remainder_block_two, remainder_block_zero,
      show 3 * n + 4 = 3 * (n + 1) + 1 by omega, remainder_block_one,
      ← add_div, ← integral_split]

private def tail (j : ℕ) : unitInterval :=
  ⟨remainder (j + 1) / remainder j,
    (div_pos (remainder_pos _) (remainder_pos _)).le, by
      apply (div_le_one (remainder_pos j)).mpr
      have hq : (1 : ℝ) ≤ partialQuotient (j + 2) := by
        exact_mod_cast one_le_partialQuotient (j + 2)
      rw [remainder_recurrence j]
      nlinarith [remainder_pos (j + 2),
        mul_nonneg (sub_nonneg.mpr hq) (remainder_pos (j + 1)).le]⟩

private theorem tail_step (c : ℝ) (hc : 1 ≤ c) (j : ℕ) :
    tail j = RealContinuedFraction.step (coefficient c hc (j + 2)) (tail (j + 1)) := by
  apply Subtype.ext
  change remainder (j + 1) / remainder j =
    1 / ((if j + 2 = 1 then c else (partialQuotient (j + 2) : ℝ)) +
      remainder (j + 1 + 1) / remainder (j + 1))
  rw [ite_eq_right (by omega : j + 2 ≠ 1)]
  have hq : (0 : ℝ) < partialQuotient (j + 2) := by
    exact_mod_cast zero_lt_one.trans_le (one_le_partialQuotient (j + 2))
  have hden := add_pos hq (div_pos (remainder_pos (j + 1 + 1)) (remainder_pos (j + 1)))
  apply (div_eq_div_iff (remainder_pos j).ne' hden.ne').mpr
  rw [remainder_recurrence j]
  field_simp [(remainder_pos (j + 1)).ne']

/-- The positive integral remainders identify the tail after the initial denominator. -/
theorem value_two (c : ℝ) (hc : 1 ≤ c) :
    (RealContinuedFraction.value (coefficient c hc) 2 : ℝ) = Real.exp 1 - 2 := by
  have expand_tail (n k : ℕ) :
      RealContinuedFraction.expand (coefficient c hc) (k + 2) n (tail (k + n)) = tail k := by
    induction n generalizing k with
    | zero => rfl
    | succ n IH =>
      rw [RealContinuedFraction.expand,
        show k + 2 + 1 = (k + 1) + 2 by omega,
        show k + (n + 1) = (k + 1) + n by omega, IH]
      exact (tail_step c hc k).symm
  have hv : RealContinuedFraction.value (coefficient c hc) 2 = tail 0 := by
    apply RealContinuedFraction.unique_value (coefficient c hc) 2
      (RealContinuedFraction.value (coefficient c hc) 2) (tail 0)
    · exact RealContinuedFraction.value_mem (coefficient c hc) 2
    · intro n
      exact ⟨tail n, by simpa using expand_tail n 0⟩
  rw [hv]
  change remainder 1 / remainder 0 = Real.exp 1 - 2
  rw [remainder_one, remainder_zero, div_one]

/-- The first denominator may be replaced by any real `c ≥ 1`. -/
theorem value_one (c : ℝ) (hc : 1 ≤ c) :
    (RealContinuedFraction.value (coefficient c hc) 1 : ℝ) = 1 / (Real.exp 1 + c - 2) := by
  rw [RealContinuedFraction.value_coe]
  change 1 / (c + (RealContinuedFraction.value (coefficient c hc) 2 : ℝ)) = _
  rw [value_two]
  congr 1
  ring

end

end SampLib.EulerContinuedFraction
