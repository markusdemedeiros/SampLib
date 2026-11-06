import SampLib.Distributions.RealEnclosure

/-! # The factorial enclosures of Euler's number

The integer recurrence accumulates the partial exponential series over `m!`.
At `m ≥ 1`, the remaining tail is at most `1 / (m * m!)`.
-/

open Finset

namespace SampLib.EulerEnclosure

noncomputable section

/-- Numerator of the exponential series through degree `m`, over `m!`. -/
def numerator : ℕ → ℕ
  | 0 => 1
  | m + 1 => numerator m * (m + 1) + 1

theorem numerator_ratio (m : ℕ) :
    (numerator m : ℝ) / m.factorial = ∑ k ∈ range (m + 1), (1 : ℝ) / k.factorial := by
  induction m with
  | zero => simp [numerator]
  | succ m IH =>
    rw [sum_range_succ, ← IH]
    simp only [numerator, Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp

theorem lower_bound (m : ℕ) : (numerator m : ℝ) / m.factorial ≤ Real.exp 1 := by
  rw [numerator_ratio]
  simpa using Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) (m + 1)

theorem upper_bound (m : ℕ) (hm : 0 < m) :
    Real.exp 1 ≤ (numerator m : ℝ) / m.factorial + 1 / ((m : ℝ) * m.factorial) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hm
  simp only [one_pow] at h
  rw [numerator_ratio, sum_range_succ]
  simpa only [one_pow, Nat.cast_add, Nat.cast_one] using h.trans_eq (by
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    have hm' : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring)

/-- The exact integer triple returned by `eBounds n`, with `m = n+1`. -/
def interval (n : ℕ) : RealEnclosure.Interval (Real.exp 1) where
  lower := (n + 1) * numerator (n + 1)
  upper := (n + 1) * numerator (n + 1) + 1
  denominator := (n + 1) * (n + 1).factorial
  positive := by positivity
  below := by
    have h := lower_bound (n + 1)
    have hp : (0 : ℝ) < (n + 1).factorial := by positivity
    have hm : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_iff₀ hp] at h
    push_cast
    nlinarith
  above := by
    have h := upper_bound (n + 1) (Nat.succ_pos _)
    have hp : (0 : ℝ) < (n + 1).factorial := by positivity
    have hm : (0 : ℝ) < n + 1 := by positivity
    have heq : (numerator (n + 1) : ℝ) / (n + 1).factorial +
        1 / (((n + 1 : ℕ) : ℝ) * (n + 1).factorial) =
        (((n + 1 : ℕ) : ℝ) * numerator (n + 1) + 1) /
          (((n + 1 : ℕ) : ℝ) * (n + 1).factorial) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)] at h
    push_cast at h ⊢
    exact h

theorem numerator_ge_two_factorial (n : ℕ) :
    2 * (n + 1).factorial ≤ numerator (n + 1) := by
  induction n with
  | zero => norm_num [numerator]
  | succ n IH =>
    have h := Nat.mul_le_mul_right (n + 2) IH
    change 2 * ((n + 2) * (n + 1).factorial) ≤
      numerator (n + 1) * (n + 2) + 1
    nlinarith

/-- Every concrete lower endpoint is at least two, including the initial enclosure. -/
theorem lower_ge_two (n : ℕ) :
    2 * ((interval n).denominator : ℤ) ≤ (interval n).lower := by
  have h := Nat.mul_le_mul_left (n + 1) (numerator_ge_two_factorial n)
  change 2 * (((n + 1) * (n + 1).factorial : ℕ) : ℤ) ≤
    ((n + 1 : ℕ) : ℤ) * (numerator (n + 1) : ℤ)
  exact_mod_cast (by nlinarith : 2 * ((n + 1) * (n + 1).factorial) ≤
    (n + 1) * numerator (n + 1))

@[simp] theorem width (n : ℕ) :
    (interval n).width = 1 / (((n + 1 : ℕ) : ℝ) * (n + 1).factorial) := by
  simp only [RealEnclosure.Interval.width, RealEnclosure.Interval.right,
    RealEnclosure.Interval.left, interval]
  push_cast
  ring

theorem width_tendsto : Filter.Tendsto (fun n => (interval n).width)
    Filter.atTop (nhds 0) := by
  simp only [width]
  apply squeeze_zero (fun n => by positivity)
    (fun n => show 1 / (((n + 1 : ℕ) : ℝ) * (n + 1).factorial) ≤
      1 / (n + 1 : ℕ) from ?_)
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply one_div_le_one_div_of_le (by positivity)
  have hf : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  nlinarith

theorem tight : RealEnclosure.Tight interval :=
  RealEnclosure.Tight.of_tendsto interval width_tendsto

end

end SampLib.EulerEnclosure
