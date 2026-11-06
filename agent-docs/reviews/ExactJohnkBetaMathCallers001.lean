module

public import SampLib.PSRN.Laws.JohnkBeta

@[expose] public section

/-! Independent normalization and full-domain mass checks for Johnk's beta identity. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.JohnkBeta.IndependentMathReview001

/-- The derived scalar really is a proposal probability, for every positive pair of shapes. -/
theorem acceptance_le_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal (acceptance a b) ≤ 1 := by
  have : IsProbabilityMeasure (betaMeasure a 1) := isProbabilityMeasureBeta ha zero_lt_one
  have : IsProbabilityMeasure (betaMeasure b 1) := isProbabilityMeasureBeta hb zero_lt_one
  have : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  have hmass := expectation a b ha hb (fun _ => 1) measurable_const
  simp only [lintegral_one, measure_univ, mul_one] at hmass
  calc
    _ = ∫⁻ x, ∫⁻ y, accepted (fun _ => 1) (x, y) ∂betaMeasure b 1 ∂betaMeasure a 1 :=
      hmass.symm
    _ ≤ ∫⁻ _ : ℝ, ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂betaMeasure b 1 ∂betaMeasure a 1 := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases h : x + y < 1 <;> simp [accepted, h]
    _ = 1 := by simp

example : acceptance 1 1 = (1 / 2 : ℝ) := by
  rw [acceptance, beta_one 1 (by norm_num)]
  norm_num

#print axioms density_expectation
#print axioms expectation
#print axioms accepted_map
#print axioms normalized_map
#print axioms acceptance_le_one

end SampLib.JohnkBeta.IndependentMathReview001
