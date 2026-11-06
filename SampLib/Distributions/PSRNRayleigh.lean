module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! # The exponential-square-root representation of a Rayleigh variate -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.PSRNRayleigh

noncomputable section

/-- The exact latent transformation used by `PSRN.newRayleigh`. -/
def transform (x : ℝ) : ℝ := Real.sqrt (2 * x)

@[fun_prop] theorem measurable_transform : Measurable transform := by
  unfold transform
  fun_prop

/-- Unit-scale Rayleigh law. -/
def law : Measure ℝ := (expMeasure 1).map transform

instance : IsProbabilityMeasure law := by
  have := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  unfold law
  infer_instance

/-- The exponential expected credit is pulled back through the square-root map. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (transform x) ∂expMeasure 1 = ∫⁻ y, F y ∂law := by
  rw [law, lintegral_map hF measurable_transform]

private theorem preimage_Iic {t : ℝ} (ht : 0 ≤ t) :
    transform ⁻¹' Iic t = Iic (t ^ 2 / 2) := by
  ext x
  simp only [mem_preimage, mem_Iic, transform, Real.sqrt_le_left ht]
  constructor <;> intro h <;> linarith

/-- The transformation has the standard Rayleigh distribution function. -/
theorem cdf_eq (t : ℝ) : cdf law t = if 0 ≤ t then 1 - Real.exp (-(t ^ 2 / 2)) else 0 := by
  have := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  rw [cdf_eq_real, measureReal_def, law,
    Measure.map_apply measurable_transform measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · rw [preimage_Iic ht]
    rw [← measureReal_def, ← cdf_eq_real]
    rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1)]
    simp [ht, div_nonneg (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 2)]
  · have he : transform ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr ((lt_of_not_ge ht).trans_le (Real.sqrt_nonneg _))
    simp [he, ht]

end

end SampLib.PSRNRayleigh
