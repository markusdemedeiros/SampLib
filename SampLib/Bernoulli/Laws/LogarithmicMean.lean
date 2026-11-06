import SampLib.Bernoulli.Laws.LatentPower
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Bernoulli.Laws.PowerIntegral

/-! # A uniform mixture of powers is the logarithmic mean

For positive `p`, integrating `p^u` over the unit interval gives
`(p-1)/log p`, with value one at `p=1`. Bernoulli mixture identification then
preserves arbitrary output credits without subtracting infinite quantities.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.LogarithmicMean

noncomputable section

/-- The logarithmic mean of `p` and one, with its removable endpoint included. -/
def bias (p : unitInterval) (hp : 0 < (p : ℝ)) : unitInterval :=
  if h : (p : ℝ) = 1 then 1 else
    ⟨((p : ℝ) - 1) / Real.log p,
      div_nonneg_of_nonpos (sub_nonpos.mpr p.2.2) (Real.log_nonpos p.2.1 p.2.2),
      (div_le_one_of_neg (Real.log_neg hp (lt_of_le_of_ne p.2.2 h))).mpr
        (Real.log_le_sub_one_of_pos hp)⟩

/-- Scalar API without exposing the normalization proofs in the subtype constructor. -/
theorem bias_coe (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (bias p hp : ℝ) = if (p : ℝ) = 1 then 1 else ((p : ℝ) - 1) / Real.log p := by
  by_cases h : (p : ℝ) = 1 <;> simp [bias, h]

/-- Integrating in the exponent is an elementary exponential antiderivative. -/
theorem integral_power (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (∫ u : ℝ in 0..1, (p : ℝ) ^ u) = (bias p hp : ℝ) := by
  by_cases h : (p : ℝ) = 1
  · simp [bias, h]
  · simpa [bias, h] using PowerIntegral.integral_const_power hp

/-- Averaging the success probability is insensitive to the cached uniform's null endpoints. -/
theorem success_mass (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∫⁻ u, ENNReal.ofReal (FractionalPower.powerBias p (LatentBernoulli.bias u) : ℝ)
      ∂DyadicPosterior.unitLaw = ENNReal.ofReal (bias p hp : ℝ) := by
  have ha : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Ico 0 1 := by
    simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
  have hc : Continuous (fun u : ℝ => (p : ℝ) ^ u) := by
    simp_rw [Real.rpow_def_of_pos hp]
    fun_prop
  have hi : Integrable (fun u : ℝ => (p : ℝ) ^ u) DyadicPosterior.unitLaw :=
    hc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have heq : (fun u => ENNReal.ofReal
      (FractionalPower.powerBias p (LatentBernoulli.bias u) : ℝ)) =ᵐ[DyadicPosterior.unitLaw]
        (fun u => ENNReal.ofReal ((p : ℝ) ^ u)) :=
    ha.mono (fun u hu => by
      simp only [FractionalPower.powerBias, LatentBernoulli.bias_coe hu])
  rw [lintegral_congr_ae heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun u => Real.rpow_nonneg p.2.1 u)]
  congr 1
  change (∫ u in Ico (0 : ℝ) 1, (p : ℝ) ^ u) = _
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact integral_power p hp

/-- The logarithmic mean identifies the whole output law, including infinite credits. -/
theorem expectation (p : unitInterval) (hp : 0 < (p : ℝ)) (F : Bool → ℝ≥0∞) :
    LatentBernoulli.credit []
      (fun u => FractionalPower.powerBias p (LatentBernoulli.bias u))
      (fun b _ => F b) = RealCoin.credit (bias p hp) F := by
  rw [LatentBernoulli.credit, DyadicPosterior.credit, DyadicPosterior.law_nil]
  exact BernoulliMixture.expectation DyadicPosterior.unitLaw _
    (LatentPower.measurable_powerBias p LatentBernoulli.measurable_bias) _ (success_mass p hp) F

end

end SampLib.LogarithmicMean
