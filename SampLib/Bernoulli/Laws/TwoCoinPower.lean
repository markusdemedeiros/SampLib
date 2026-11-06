import SampLib.Common.Laws.FractionalPowerCore
import SampLib.Bernoulli.Laws.CoinProduct

/-! # Laws of the two-coin power factory

Each round tests the base coin, then the exponent coin and a `1/(n+1)` gate. This module
proves that one round follows the reciprocal-hazard recurrence of the fractional power law.
-/

open scoped ENNReal

namespace SampLib.TwoCoinPower

noncomputable section

/-- The output bias is the fractional power `p^q`. -/
abbrev bias := FractionalPower.powerBias

/-- Credit after the exponent coin, which then runs the `1/(n+1)` gate. -/
def exponentCredit (n : ℕ) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) : Bool → ℝ≥0∞ :=
  CoinProduct.firstCredit (FractionalPower.hazardBias 1 n) (FractionalPower.hazardCredit F c)

/-- Credit after the base coin of round `n`. -/
def firstCredit (q : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (bit : Bool) : ℝ≥0∞ :=
  if bit then F true else RealCoin.credit q (exponentCredit n F c)

/-- Testing the exponent coin and `1/(n+1)` coin is a hazard of `q/(n+1)`. -/
private theorem exponent_expectation (q : unitInterval) (n : ℕ)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit q (exponentCredit n F c) =
      RealCoin.credit (FractionalPower.hazardBias q n) (FractionalPower.hazardCredit F c) := by
  have hb : q * FractionalPower.hazardBias 1 n = FractionalPower.hazardBias q n := by
    apply Subtype.ext
    simp [FractionalPower.hazardBias, div_eq_mul_inv]
  simpa only [exponentCredit, RealCoin.lintegral_law, CoinProduct.law, hb] using
    CoinProduct.expectation_preservation q (FractionalPower.hazardBias 1 n)
      (FractionalPower.hazardCredit F c)

/-- First-round conditioning is the same power-law recurrence for arbitrary credits. -/
theorem round_expectation (p q : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ bit, firstCredit q n F c bit ∂RealCoin.law p =
      FractionalPower.exitCredit p q F n + FractionalPower.continueProb p q n * c := by
  have hfirst : firstCredit q n F c = FractionalPower.inputCredit q n F c := by
    funext bit
    cases bit <;> simp only [firstCredit, FractionalPower.inputCredit,
      Bool.false_eq_true, ite_false, ite_true, exponent_expectation]
  rw [hfirst, FractionalPower.round_expectation]

end

end SampLib.TwoCoinPower
