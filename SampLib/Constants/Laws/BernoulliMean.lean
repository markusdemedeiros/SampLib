import SampLib.Bernoulli.Laws.CoinMean

/-! # Equal mixtures of Bernoulli continuation credits -/

open scoped ENNReal

namespace SampLib.CoinMean

/-- Averaging two Bernoulli expectations averages their biases, even at infinite credit. -/
theorem credit_mean (p q : unitInterval) (F : Bool → ℝ≥0∞) :
    (RealCoin.credit p F + RealCoin.credit q F) / 2 = RealCoin.credit (bias p q) F := by
  have h := expectation_preservation p q F
  simp only [CoinConditional.firstCredit, RealCoin.lintegral_law] at h
  change ENNReal.ofReal (1 / 2 : ℝ) * RealCoin.credit p F +
    ENNReal.ofReal (1 - (1 / 2 : ℝ)) * RealCoin.credit q F = RealCoin.credit (bias p q) F at h
  norm_num [ENNReal.ofReal_div_of_pos] at h
  simpa only [ENNReal.div_eq_inv_mul, mul_add] using h

end SampLib.CoinMean
