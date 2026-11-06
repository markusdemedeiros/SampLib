import SampLib.Bernoulli.Laws.LinearFactory
import SampLib.Bernoulli.Laws.CoinMean

/-! # Laws of addition by a linear factory

The mean coin has bias `(p+q)/2`, and the linear factory with coefficient `2/1` doubles it.
The supplied margin keeps the sum strictly below one.
-/

namespace SampLib.Addition

noncomputable section

theorem mean_ratio (p q : unitInterval) :
    Gambler.ratio (CoinMean.bias p q) 2 1 = (p : ℝ) + q := by
  simp only [Gambler.ratio, CoinMean.bias, CoinConditional.bias, Set.Icc.coe_convexComb]
  norm_num [VonNeumann.fairBias]
  ring

theorem admissible (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) :
    LinearFactory.Admissible (CoinMean.bias p q) 2 1 e f := by
  refine ⟨by norm_num, by norm_num, fun _ => ⟨he, hef, ?_⟩⟩
  simpa only [mean_ratio] using h

/-- The sum bias, normalized by the supplied strict upper margin. -/
def bias (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) : unitInterval :=
  LinearFactory.bias (CoinMean.bias p q) 2 1 e f (admissible p q e f he hef h)

theorem bias_coe (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ) + q ≤ 1 - (e : ℝ) / f) : (bias p q e f he hef h : ℝ) = (p : ℝ) + q := by
  exact mean_ratio p q

end

end SampLib.Addition
