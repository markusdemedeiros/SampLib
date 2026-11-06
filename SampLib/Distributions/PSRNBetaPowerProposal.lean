module

public import SampLib.Distributions.PSRNBetaRejection

@[expose] public section

/-! # Beta rejection from a power-uniform proposal

A Beta(a,1) proposal already supplies x^(a−1). The remaining conditional
acceptance probability supplies (1−x)^(b−1), including when a is subunit.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SampLib.PSRNBetaPowerProposal

noncomputable section

def weight (b x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then (1 - x) ^ (b - 1) else 0

theorem measurable_weight (b : ℝ) : Measurable (weight b) := by
  exact Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

theorem weight_nonneg (b x : ℝ) : 0 ≤ weight b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simpa only [weight, ite_eq_left hx] using
      Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (b - 1)
  · simp [weight, hx]

theorem weight_mem {b : ℝ} (hb : 1 ≤ b) (x : ℝ) : weight b x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [weight, ite_eq_left hx, mem_Icc]
    exact ⟨Real.rpow_nonneg (by linarith) _,
      Real.rpow_le_one (by linarith) (by linarith) (by linarith)⟩
  · simp [weight, hx]

theorem density_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    weight b x * betaPDFReal a 1 x =
      (beta a b / beta a 1) * betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [weight, betaPDFReal, ite_eq_left hx, sub_self, Real.rpow_zero, mul_one]
    field_simp [ne_of_gt (beta_pos ha hb), ne_of_gt (beta_pos ha zero_lt_one)]
  · simp [weight, betaPDFReal, hx]

/-- The proposal's credit after acceptance is exactly a positive multiple of Beta(a,b). -/
theorem acceptance_expectation {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, ENNReal.ofReal (weight b x) * F x ∂betaMeasure a 1 =
      ENNReal.ofReal (beta a b / beta a 1) * ∫⁻ x, F x ∂betaMeasure a b := by
  have hweight : Measurable (fun x => ENNReal.ofReal (weight b x)) :=
    ENNReal.measurable_ofReal.comp (measurable_weight b)
  have hkernel : Measurable (fun x => ENNReal.ofReal (weight b x) * F x) := hweight.mul hF
  have hpdf (c : ℝ) : Measurable (betaPDF a c) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a c)
  have hconst : 0 ≤ beta a b / beta a 1 :=
    (div_pos (beta_pos ha hb) (beta_pos ha zero_lt_one)).le
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (hpdf 1) hkernel,
    betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (hpdf b) hF]
  have hpoint (x : ℝ) : betaPDF a 1 x * (ENNReal.ofReal (weight b x) * F x) =
      ENNReal.ofReal (beta a b / beta a 1) * (betaPDF a b x * F x) := by
    rw [← mul_assoc, mul_comm (betaPDF a 1 x), betaPDF,
      ← ENNReal.ofReal_mul (weight_nonneg b x), density_identity ha hb x,
      ENNReal.ofReal_mul hconst, mul_assoc]
    rfl
  simp only [Pi.mul_apply]
  rw [lintegral_congr hpoint]
  exact lintegral_const_mul _ ((hpdf b).mul hF)

/-- The positive normalization is precisely the proposal's acceptance probability. -/
theorem acceptance_mass {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, ENNReal.ofReal (weight b x) ∂betaMeasure a 1 =
      ENNReal.ofReal (beta a b / beta a 1) := by
  have := isProbabilityMeasureBeta ha hb
  simpa only [mul_one, lintegral_one, measure_univ] using
    acceptance_expectation ha hb (fun _ => 1) measurable_const


end

end SampLib.PSRNBetaPowerProposal
