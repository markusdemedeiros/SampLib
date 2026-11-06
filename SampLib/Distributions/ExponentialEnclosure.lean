module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! # Rational Taylor enclosures of a negative exponential

Taylor's mean-value remainder is the next term times a number in `[0,1]`.
Thus neighboring partial sums enclose `exp(-r)` even before the terms decrease.
-/

open Finset Set

namespace SampLib.ExponentialEnclosure

noncomputable section

def partialSum (r : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), (-r) ^ k / k.factorial

private theorem taylor_exp (r : ℝ) (hr : 0 < r) (n : ℕ) :
    taylorWithinEval Real.exp n (uIcc 0 (-r)) 0 (-r) = partialSum r n := by
  induction n with
  | zero => simp [partialSum]
  | succ n IH =>
    rw [taylorWithinEval_succ, IH]
    have hderiv : iteratedDerivWithin (n + 1) Real.exp (uIcc 0 (-r)) 0 = 1 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith))
        Real.contDiff_exp.contDiffAt (left_mem_uIcc), iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.exp_zero]
    rw [hderiv]
    simp [partialSum, sum_range_succ, Nat.factorial_succ, div_eq_mul_inv, mul_comm]

/-- The remainder has the next term's sign and at most its magnitude. -/
theorem remainder (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ∃ θ ∈ Icc (0 : ℝ) 1,
      Real.exp (-r) - partialSum r n = θ * ((-r) ^ (n + 1) / (n + 1).factorial) := by
  rcases hr.eq_or_lt with rfl | hr
  · refine ⟨0, by simp, ?_⟩
    simp [partialSum, sum_range_succ']
  · obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.exp) (n := n) (x₀ := 0) (x := -r) (by linarith)
      Real.contDiff_exp.contDiffOn
    refine ⟨Real.exp z, ⟨(Real.exp_pos _).le, ?_⟩, ?_⟩
    · have hz' : z ∈ Ioo (-r) 0 := by
        simpa only [uIoo_of_gt (neg_lt_zero.mpr hr)] using hz
      exact Real.exp_le_one_iff.mpr hz'.2.le
    · simpa only [taylor_exp r hr n, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
        sub_zero, mul_div_assoc] using heq

/-- Exact integer power and common-denominator accumulators used by the oracle. -/
def denominator (y k : ℕ) : ℕ := y ^ k * k.factorial

def numerator (x y : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => numerator x y k * (y * (k + 1)) + (-(x : ℤ)) ^ (k + 1)

theorem denominator_positive (y k : ℕ) (hy : 0 < y) : 0 < denominator y k := by
  unfold denominator
  positivity

theorem numerator_ratio (x y k : ℕ) (hy : 0 < y) :
    (numerator x y k : ℝ) / denominator y k = partialSum ((x : ℝ) / y) k := by
  induction k with
  | zero => simp [numerator, denominator, partialSum]
  | succ k IH =>
    rw [partialSum, sum_range_succ, ← partialSum, ← IH]
    rw [← neg_div, div_pow]
    simp only [numerator, denominator, Nat.factorial_succ, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_natCast, pow_succ]
    have hy' : (y : ℝ) ≠ 0 := by positivity
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hkp : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

end

end SampLib.ExponentialEnclosure
