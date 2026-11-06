import SampLib.Distributions.JohnkBeta

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace JohnkBetaAuthorCallers

open SampLib.JohnkBeta

noncomputable section

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, (if x + y < 1 then F (x / (x + y)) else 0)
      ∂betaMeasure b 1 ∂betaMeasure a 1) =
      ENNReal.ofReal (acceptance a b) * ∫⁻ u, F u ∂betaMeasure a b :=
  expectation a b ha hb F hF

example : acceptance 1 1 = 1/2 := by norm_num [acceptance, beta_one]

example : (((betaMeasure (1/3) 1).prod (betaMeasure (2/5) 1)).restrict
    {z : ℝ × ℝ | z.1 + z.2 < 1}).map
      (fun z : ℝ × ℝ => z.1 / (z.1 + z.2)) =
    ENNReal.ofReal (acceptance (1/3) (2/5)) • betaMeasure (1/3) (2/5) :=
  accepted_map _ _ (by norm_num) (by norm_num)

example : (ENNReal.ofReal (acceptance 2 3))⁻¹ •
    ((((betaMeasure 2 1).prod (betaMeasure 3 1)).restrict
      {z : ℝ × ℝ | z.1 + z.2 < 1}).map
        (fun z : ℝ × ℝ => z.1 / (z.1 + z.2))) = betaMeasure 2 3 :=
  normalized_map _ _ (by norm_num) (by norm_num)

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ x, ∫⁻ y, (if x + y < 1 then ∞ else 0 : ℝ≥0∞)
      ∂betaMeasure b 1 ∂betaMeasure a 1) = ∞ := by
  let := isProbabilityMeasureBeta ha hb
  have h := expectation a b ha hb (fun _ => ∞) measurable_const
  simpa only [accepted, lintegral_const, measure_univ, mul_one,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr (acceptance_pos a b ha hb)).ne'] using h

private def impossible (x : ℝ) : ℝ≥0∞ := if x ≤ 0 then ∞ else 0

private theorem measurable_impossible : Measurable impossible :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ x, ∫⁻ y, accepted impossible (x, y)
      ∂betaMeasure b 1 ∂betaMeasure a 1) = 0 := by
  rw [expectation a b ha hb impossible measurable_impossible]
  have hz : (∫⁻ x, impossible x ∂betaMeasure a b) = 0 := by
    have hβ : Measurable (betaPDF a b) :=
      ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
    rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hβ measurable_impossible]
    calc
      _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr
        intro x
        by_cases hx : x ≤ 0
        · simp [impossible, hx, betaPDF_eq_zero_of_nonpos hx]
        · simp [impossible, hx]
      _ = 0 := lintegral_zero
  rw [hz, mul_zero]

example (F : ℝ → ℝ≥0∞) : accepted F (1/3, 2/3) = 0 := by
  norm_num [accepted]

example : 0 < acceptance (1/1000) (999/1000) := acceptance_pos _ _ (by norm_num)
  (by norm_num)

#print axioms beta_one
#print axioms power_density
#print axioms radial_density
#print axioms density_expectation
#print axioms expectation
#print axioms accepted_map
#print axioms normalized_map
#print axioms acceptance_pos

end
end JohnkBetaAuthorCallers
