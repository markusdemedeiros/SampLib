import SampLib.Bernoulli.Laws.CoinConditional
import SampLib.Bernoulli.Laws.VonNeumann

/-! # Laws of the coin mean

A fair selector turns conditional mixing into the arithmetic mean `(p+q)/2`.
-/

open scoped ENNReal

namespace SampLib.CoinMean

noncomputable section

/-- The equally weighted bias `(p+q)/2`. -/
abbrev bias (p q : unitInterval) := CoinConditional.bias p q VonNeumann.fairBias

abbrev law (p q : unitInterval) := RealCoin.law (bias p q)

/-- Specializing conditional mixing to a fair selector gives the arithmetic mean. -/
theorem expectation_preservation (p q : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ a, CoinConditional.firstCredit p q F a ∂RealCoin.law VonNeumann.fairBias =
      ∫⁻ b, F b ∂law p q :=
  CoinConditional.expectation_preservation p q VonNeumann.fairBias F

end

end SampLib.CoinMean
