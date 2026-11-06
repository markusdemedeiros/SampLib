module

public import SampLib.PSRN.Laws.ReciprocalUniform

@[expose] public section

/-! Boundary masses and null infinite credits for the canonical reciprocal-uniform law. -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.ReciprocalUniform.ProducerCallers

example : law univ = 1 := measure_univ

example : law (Iic (-3)) = 0 := by norm_num [law_Iic]
example : law (Iic 0) = 0 := by norm_num [law_Iic]
example : law (Iic 1) = 0 := by norm_num [law_Iic]
example : law (Iic 2) = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [law_Iic]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

example : ProbabilityTheory.paretoMeasure 1 1 (Iic 2) = (2 : ℝ≥0∞)⁻¹ := by
  rw [← law_eq_pareto]
  norm_num [law_Iic]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

example : (∫⁻ x, (Iic (1 : ℝ)).indicator (fun _ => (∞ : ℝ≥0∞)) x ∂law) = 0 := by
  rw [lintegral_indicator_const measurableSet_Iic, law_Iic]
  norm_num

example : (∫⁻ _ : ℝ, (∞ : ℝ≥0∞) ∂law) = ∞ := by simp

example (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂ProbabilityTheory.paretoMeasure 1 1) =
      ∫⁻ u in Ico (0 : ℝ) 1, F (1 / u) := by
  rw [← law_eq_pareto]
  exact expectation F hF

#print axioms law_eq_pareto
#print axioms law_Iic
#print axioms expectation

end SampLib.ReciprocalUniform.ProducerCallers
