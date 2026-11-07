import SampLib.Bernoulli.Laws.AlternatingSeriesMean

/-! # Pairing the factorial coefficients of `exp(p²)(1-p)` -/

open Filter
open scoped Topology

namespace SampLib.ExpSquareComplement

noncomputable section

def parameters : AlternatingSeries.Parameters where
  coefficient n := 1 / ((n / 2).factorial : ℚ)
  nonnegative n := by positivity
  decreasing := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.div_le_div_right hij)
  initial := by norm_num
  vanishes := by
    have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
      refine tendsto_atTop.2 fun n => ?_
      exact eventually_atTop.2 ⟨2 * n, fun k hk => by omega⟩
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (factorial_tendsto_atTop.comp hdiv)

/-- Each even term and its odd successor share a factorial denominator. -/
theorem hasSum (p : ℝ) :
    HasSum (fun n => AlternatingEnclosure.sign n * p ^ n *
      AlternatingSeries.value parameters n) ((1 - p) * Real.exp (p ^ 2)) := by
  have he : HasSum (fun n : ℕ => (p ^ 2) ^ n / n.factorial) (Real.exp (p ^ 2)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (p ^ 2)
  have heven : HasSum (fun n => AlternatingEnclosure.sign (2 * n) * p ^ (2 * n) *
      AlternatingSeries.value parameters (2 * n)) (Real.exp (p ^ 2)) := by
    simpa [parameters, AlternatingSeries.value, AlternatingEnclosure.sign_eq,
      pow_mul, div_eq_mul_inv] using he
  have hodd : HasSum (fun n => AlternatingEnclosure.sign (2 * n + 1) * p ^ (2 * n + 1) *
      AlternatingSeries.value parameters (2 * n + 1)) (-p * Real.exp (p ^ 2)) := by
    convert he.mul_left (-p) using 1
    funext n
    simp only [AlternatingSeries.value, parameters, AlternatingEnclosure.sign_eq,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [show (2 * n + 1) / 2 = n by omega]
    simp [pow_add, pow_mul, div_eq_mul_inv]
    ring
  convert HasSum.even_add_odd (f := fun n => AlternatingEnclosure.sign n * p ^ n *
    AlternatingSeries.value parameters n) heven hodd using 1
  ring

/-- The alternating-series engine therefore samples the advertised exponential polynomial. -/
theorem bias_coe (p : unitInterval) :
    (AlternatingSeries.meanBias parameters p : ℝ) = Real.exp ((p : ℝ) ^ 2) * (1 - p) := by
  rw [AlternatingSeries.mean_eq_of_hasSum parameters p _ (hasSum p)]
  ring

end

end SampLib.ExpSquareComplement
