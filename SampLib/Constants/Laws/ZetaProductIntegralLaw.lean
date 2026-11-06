import SampLib.Constants.Laws.ZetaProductIntegral
import SampLib.Constants.Laws.ZetaRelated

/-! # The advertised eta law of Occil's zeta-related coin -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ZetaRelated

noncomputable section

/-- The total conditional success probability is bounded by one under the initial joint law. -/
theorem integrable_conditionalBias (n : ℕ) :
    Integrable (fun u => (conditionalBias n u : ℝ))
      (UniformVector.law (UniformVector.initial n)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_conditionalBias n).subtype_coe.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (conditionalBias n u).2.1]
    exact (conditionalBias n u).2.2

/-- The scalar marginal, normalized before identifying its closed form. -/
def marginalBias (n : ℕ) : unitInterval :=
  ⟨∫ u, (conditionalBias n u : ℝ) ∂UniformVector.law (UniformVector.initial n),
    integral_nonneg (fun u => (conditionalBias n u).2.1), by
      have h := integral_mono (integrable_conditionalBias n)
        (integrable_const (1 : ℝ)) (fun u => (conditionalBias n u).2.2)
      simpa using h⟩

/-- The interval projection disappears almost surely in every independent uniform coordinate. -/
theorem conditionalBias_ae (n : ℕ) :
    (fun u => (conditionalBias n u : ℝ)) =ᵐ[UniformVector.law (UniformVector.initial n)]
      (fun u => 1 / (1 + ZetaProductIntegral.product u)) := by
  filter_upwards [ZetaProductIntegral.ae_coordinates n] with u hu
  have hprod : (UniformVector.productBias (List.ofFn id) u : ℝ) =
      ZetaProductIntegral.product u := by
    simp only [UniformVector.productBias, UniformVector.coinBias, List.map_ofFn,
      Function.comp_def, id_eq, List.prod_ofFn, ZetaProductIntegral.product]
    change (Set.Icc.coeMonoidWithZeroHom (∏ i, LatentBernoulli.bias (u i)) : ℝ) = _
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => LatentBernoulli.bias_coe (hu i))
  simpa only [conditionalBias, LatentReal.CoinReciprocal.bias, OneDivOnePlus.bias,
    EvenParity.bias] using congrArg (fun x : ℝ => 1 / (1 + x)) hprod

/-- The advertised `η(n) = (1 - 2^(1-n)) ζ(n)` law, throughout the source's domain `n ≥ 2`. -/
theorem marginalBias_coe {n : ℕ} (hn : 2 ≤ n) :
    (marginalBias n : ℝ) =
      (1 - (2 : ℝ) ^ (1 - (n : ℝ))) * (riemannZeta n).re := by
  change (∫ u, (conditionalBias n u : ℝ) ∂UniformVector.law (UniformVector.initial n)) = _
  rw [integral_congr_ae (conditionalBias_ae n)]
  exact (ZetaProductIntegral.integral_eq_zeta hn).trans
    (congrArg (fun x : ℝ => x * (riemannZeta n).re) (ZetaProductIntegral.eta_factor n))

/-- Only a finite scalar probability is converted from the real integral. -/
theorem mass_true (n : ℕ) :
    ConditionalCoin.mass (UniformVector.law (UniformVector.initial n))
      (conditionalBias n) true = ENNReal.ofReal (marginalBias n : ℝ) := by
  simp only [ConditionalCoin.mass, RealCoin.pmf, ite_true]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_conditionalBias n)
    (Filter.Eventually.of_forall fun u => (conditionalBias n u).2.1)).symm

/-- The operationally obtained mixture is the normalized eta Bernoulli law. -/
theorem law_eq_coin (n : ℕ) : law n = RealCoin.law (marginalBias n) :=
  ConditionalCoin.law_eq_coin _ _ (measurable_conditionalBias n) _ (mass_true n)

/-- Marginalization preserves arbitrary infinite Boolean continuation credits. -/
theorem expectation_eta (n : ℕ) (F : Bool → ℝ≥0∞) :
    LatentReal.LatentCoin.credit (UniformVector.world n) (UniformVector.initial n)
      (conditionalBias n) (fun b _ => F b) = RealCoin.credit (marginalBias n) F := by
  rw [← expectation, law_eq_coin, RealCoin.lintegral_law]

end

end SampLib.ZetaRelated
