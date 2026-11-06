module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Integer beta CDFs as binomial tails

The derivative of a tail of Bernstein polynomials telescopes to its first boundary term.
The beta normalizer identifies that term with the integer-shape beta density.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Polynomial

namespace SampLib.IntegerBetaCDF

noncomputable section

/-- The probability of at least `k` successes in `n` Bernoulli trials. -/
def tail (n k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j)

private def tailPolynomial (n k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

private theorem tailPolynomial_eval (n k : ℕ) (x : ℝ) :
    (tailPolynomial n k).eval x = tail n k x := by
  simp [tailPolynomial, tail, Polynomial.eval_finsetSum, bernsteinPolynomial]

private theorem tailPolynomial_zero (n k : ℕ) (hk : 0 < k) :
    (tailPolynomial n k).eval 0 = 0 := by
  simp only [tailPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [bernsteinPolynomial.eval_at_0]
  exact ite_eq_right (by have := (Finset.mem_Icc.mp hj).1; omega)

private theorem derivative_tailPolynomial (n k : ℕ) (hk : k ≤ n) :
    (tailPolynomial (n + 1) (k + 1)).derivative =
      (n + 1) * bernsteinPolynomial ℝ n k := by
  unfold tailPolynomial
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.sum_Ico_add' (fun j => bernsteinPolynomial ℝ (n + 1) j) k (n + 1) 1]
  simp only [Polynomial.derivative_sum, bernsteinPolynomial.derivative_succ_aux,
    ← Finset.mul_sum]
  congr 1
  have h := Finset.sum_Ico_sub (fun j => bernsteinPolynomial ℝ n j) (by omega : k ≤ n + 1)
  calc
    _ = -(∑ j ∈ Finset.Ico k (n + 1),
        (bernsteinPolynomial ℝ n (j + 1) - bernsteinPolynomial ℝ n j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact (neg_sub _ _).symm
    _ = _ := by rw [h, bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : n < n + 1)]; simp

private theorem normalizer (a b : ℕ) :
    1 / beta (a + 1) (b + 1) =
      ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) := by
  have hfactorial := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  have hcast : ((a + b).choose a : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) =
      ((a + b).factorial : ℝ) := by
    exact_mod_cast (by simpa using hfactorial)
  have ha : (a.factorial : ℝ) ≠ 0 := by positivity
  have hb : (b.factorial : ℝ) ≠ 0 := by positivity
  have hab : ((a + b).factorial : ℝ) ≠ 0 := by positivity
  rw [beta, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  have hs : (a : ℝ) + 1 + ((b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hs, Real.Gamma_nat_eq_factorial, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp
  nlinarith [hcast]

private def density (a b : ℕ) (x : ℝ) : ℝ :=
  ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * x ^ a * (1 - x) ^ b

@[fun_prop] private theorem continuous_density (a b : ℕ) : Continuous (density a b) := by
  unfold density
  fun_prop

private theorem density_nonneg (a b : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ density a b x := by
  have hzero := hx.1
  have hone : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  unfold density
  positivity

private theorem hasDerivAt_tail (a b : ℕ) (x : ℝ) :
    HasDerivAt (tail (a + b + 1) (a + 1)) (density a b x) x := by
  have h := (tailPolynomial (a + b + 1) (a + 1)).hasDerivAt x
  rw [derivative_tailPolynomial (a + b) a (by omega)] at h
  simpa [tailPolynomial_eval, density, bernsteinPolynomial, Nat.add_sub_cancel_left,
    mul_assoc] using h

private theorem betaPDF_eq_indicator (a b : ℕ) :
    betaPDF (a + 1) (b + 1) =
      (Ioo (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (density a b x)) := by
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hx, betaPDF_of_pos_lt_one hx.1 hx.2]
    simp only [add_sub_cancel_right, Real.rpow_natCast, normalizer, density]
  · simp [betaPDF, betaPDFReal, show ¬(0 < x ∧ x < 1) from hx, hx]

/-- The integrated integer beta density is its binomial tail. -/
private theorem betaMeasure_Iic_shifted (a b : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    betaMeasure (a + 1) (b + 1) (Iic x) =
      ENNReal.ofReal (tail (a + b + 1) (a + 1) x) := by
  rw [betaMeasure, betaPDF_eq_indicator, withDensity_indicator measurableSet_Ioo,
    restrict_Ioo_eq_restrict_Icc, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hinter : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 x := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hy, hzero, _⟩
      exact ⟨hzero, hy⟩
    · rintro ⟨hzero, hy⟩
      exact ⟨hy, hzero, hy.trans hx.2⟩
  have hi : IntegrableOn (density a b) (Icc 0 x) :=
    (by fun_prop : Continuous (density a b)).integrableOn_Icc
  rw [hinter, ← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Icc
      (fun y hy => density_nonneg a b ⟨hy.1, hy.2.trans hx.2⟩)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1]
  congr 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_tail a b y)
    (Continuous.intervalIntegrable (by fun_prop : Continuous (density a b)) 0 x)
  simpa [← tailPolynomial_eval, tailPolynomial_zero _ _ (by omega : 0 < a + 1)] using h

/-- A positive success threshold is impossible at bias zero. -/
theorem tail_zero (n k : ℕ) (hk : 0 < k) : tail n k 0 = 0 := by
  rw [← tailPolynomial_eval, tailPolynomial_zero n k hk]

/-- An admissible success threshold is certain at bias one. -/
theorem tail_one (n k : ℕ) (hk : k ≤ n) : tail n k 1 = 1 := by
  rw [← tailPolynomial_eval]
  simp [tailPolynomial, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_1, hk]

/-- Integer beta CDFs are binomial upper-tail probabilities, including both endpoints. -/
theorem betaMeasure_Iic (n k : ℕ) (hk : 0 < k ∧ k ≤ n)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    betaMeasure (k : ℝ) ((n + 1 - k : ℕ) : ℝ) (Iic x) =
      ENNReal.ofReal (tail n k x) := by
  have hn : k - 1 + (n - k) + 1 = n := by omega
  have hk' : k - 1 + 1 = k := by omega
  have hb : n - k + 1 = n + 1 - k := by omega
  simpa only [hn, ← Nat.cast_add_one, hk', hb] using
    betaMeasure_Iic_shifted (k - 1) (n - k) x hx

end

end SampLib.IntegerBetaCDF
