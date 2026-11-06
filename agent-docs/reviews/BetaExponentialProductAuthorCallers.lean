import SampLib.PSRN.Laws.BetaExponentialProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BetaExponentialProductAuthorCallers

noncomputable section

open SampLib.BetaExponentialProduct

example (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, ∫⁻ s, F (u * s) ∂gammaMeasure (a + b) r ∂betaMeasure a b) =
      ∫⁻ x, F x ∂gammaMeasure a r := expectation_gamma a b r ha hb hr F hF

example : ((betaMeasure 1 1).prod (gammaMeasure 2 3)).map
    (fun z : ℝ × ℝ => z.1 * z.2) = gammaMeasure 1 3 := by
  convert beta_mul_gamma 1 1 3 (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

example : ((betaMeasure (1/2) (1/2)).prod (expMeasure 2)).map
    (fun z : ℝ × ℝ => z.1 * z.2) = gammaMeasure (1/2) 2 := by
  convert beta_mul_exponential (1/2) 2 (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

example (a r : ℝ) (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r) :
    (∫⁻ _u, ∫⁻ _s, (∞ : ℝ≥0∞) ∂expMeasure r ∂betaMeasure a (1-a)) =
      ∫⁻ _x, (∞ : ℝ≥0∞) ∂gammaMeasure a r :=
  expectation a r ha ha1 hr _ measurable_const

private def impossible (x : ℝ) : ℝ≥0∞ := if x < 0 then ∞ else 0

private theorem measurable_impossible : Measurable impossible :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

private theorem gamma_impossible (a r : ℝ) :
    (∫⁻ x, impossible x ∂gammaMeasure a r) = 0 := by
  have hγ : Measurable (gammaPDF a r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hγ measurable_impossible]
  calc
    _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro x
      by_cases hx : x < 0
      · simp [impossible, hx, gammaPDF_of_neg hx]
      · simp [impossible, hx]
    _ = 0 := lintegral_zero

example (a r : ℝ) (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r) :
    (∫⁻ u, ∫⁻ s, impossible (u * s) ∂expMeasure r ∂betaMeasure a (1-a)) = 0 := by
  rw [expectation a r ha ha1 hr impossible measurable_impossible]
  exact gamma_impossible a r

#print axioms density_factor_real
#print axioms density_factor
#print axioms gamma_pair_transform
#print axioms expectation_gamma
#print axioms beta_mul_gamma
#print axioms beta_mul_exponential
#print axioms expectation

end

end BetaExponentialProductAuthorCallers
