import SampLib.Bernoulli.Laws.AlternatingSeries
import SampLib.Bernoulli.Laws.TrigonometricFactorySeries

/-! # Rational coefficient parameters for the trigonometric series engine -/

open Filter
open scoped Topology

namespace SampLib.TrigonometricFactoryParameters

noncomputable section

open TrigonometricFactorySeries

def cosine : AlternatingSeries.Parameters where
  coefficient n := 1 / (2 * n).factorial
  nonnegative n := by positivity
  decreasing := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_left 2 hij)
  initial := by norm_num
  vanishes := by
    convert (FactorialSeries.coefficient_summable .cos).tendsto_atTop_zero using 1
    ext n
    simp [FactorialSeries.coefficient, FactorialSeries.denominator, FactorialSeries.degree]

def sinc (c : ℚ) (hc : 0 ≤ c) (hc6 : c ≤ 6) : AlternatingSeries.Parameters where
  coefficient n := c ^ n / (2 * n + 1).factorial
  nonnegative n := by positivity
  decreasing := by
    intro i j hij
    have h := sincCoefficient_antitone (c := (c : ℝ)) (by exact_mod_cast hc)
      (by exact_mod_cast hc6) hij
    unfold sincCoefficient at h
    exact_mod_cast h
  initial := by norm_num
  vanishes := by
    convert sincCoefficient_vanishes (c := (c : ℝ)) (by exact_mod_cast hc) using 1
    ext n
    simp [sincCoefficient]

theorem cosine_mean_coe (p : unitInterval) :
    (AlternatingSeries.meanBias cosine p : ℝ) = Real.cos (Real.sqrt p) := by
  apply AlternatingSeries.mean_eq_of_hasSum
  convert hasSum_cosineSqrt p.2.1 using 1
  ext n
  simp [AlternatingSeries.value, cosine, FactorialSeries.coefficient,
      FactorialSeries.denominator, FactorialSeries.degree]

theorem sinc_mean_coe (c : ℚ) (hc : 0 ≤ c) (hc6 : c ≤ 6) (p : unitInterval) :
    (AlternatingSeries.meanBias (sinc c hc hc6) p : ℝ) =
      Real.sinc (Real.sqrt ((c : ℝ) * p)) := by
  apply AlternatingSeries.mean_eq_of_hasSum
  convert hasSum_sincSqrt (c := (c : ℝ)) (by exact_mod_cast hc) p.2.1 using 1
  ext n
  simp [AlternatingSeries.value, sinc, sincCoefficient]

/-- Two input flips replace p by p², restoring the source's p sqrt(c) argument. -/
theorem sinc_scaled_mean_coe (c : ℚ) (hc : 0 ≤ c) (hc6 : c ≤ 6) (p : unitInterval) :
    (AlternatingSeries.meanBias (sinc c hc hc6) (p * p) : ℝ) =
      Real.sinc ((p : ℝ) * Real.sqrt c) := by
  rw [sinc_mean_coe]
  change Real.sinc (Real.sqrt ((c : ℝ) * ((p : ℝ) * p))) = _
  rw [← pow_two, Real.sqrt_mul (by exact_mod_cast hc), Real.sqrt_sq_eq_abs,
    abs_of_nonneg p.2.1, mul_comm]

end

end SampLib.TrigonometricFactoryParameters
