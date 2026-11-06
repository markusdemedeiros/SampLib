import SampLib.Distributions.ArcsineFactoryParameters
import SampLib.Samplers.FractionalPower
import SampLib.Samplers.CoinMean

/-! The fair arcsine mixture cancels the complementary square-root term. -/

namespace SampLib.ArcsineFactories

noncomputable section

abbrev rootBias (p : unitInterval) : unitInterval :=
  FractionalPower.bias (unitInterval.symm (p * p)) 1 2 (by decide) (by decide)

def halfBias (p : unitInterval) : unitInterval :=
  CoinMean.bias (ArcsineFactoryParameters.bias p) (unitInterval.symm (rootBias p))

/-- The fair mixture cancels the complementary square-root contribution. -/
theorem halfBias_coe (p : unitInterval) : (halfBias p : ℝ) = Real.arcsin p / 2 := by
  have hr : (rootBias p : ℝ) = Real.sqrt (1 - (p : ℝ) ^ 2) := by
    simp only [rootBias, FractionalPower.bias, FractionalPower.powerBias,
      FractionalPower.exponent, unitInterval.coe_symm_eq, Set.Icc.coe_mul]
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    rw [← Real.sqrt_eq_rpow]
    congr 1
    ring
  simp only [halfBias, CoinMean.bias, CoinConditional.bias, Set.Icc.coe_convexComb,
    unitInterval.coe_symm_eq, VonNeumann.fairBias, hr, ArcsineFactoryParameters.bias_coe]
  ring

end

end SampLib.ArcsineFactories
