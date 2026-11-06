module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # Adding one exponential to a positive-shape gamma law

The common exponential factor leaves the power integral `∫₀ˣ y^(shape-1)dy`.
Gamma's recurrence absorbs its denominator. The resulting measure identity
transports arbitrary nonnegative continuation credits, including infinite ones.
-/

open Set MeasureTheory ProbabilityTheory Real
open ENNReal (ofReal)
open scoped ENNReal MeasureTheory

namespace SampLib.GammaSuccessor

noncomputable section

private theorem measurable_pdf (shape rate : ℝ) : Measurable (gammaPDF shape rate) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal shape rate)

/-- The integrable power singularity at zero needs only a positive shape. -/
theorem power_mass (shape : ℝ) (hshape : 0 < shape) (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ y in Icc 0 z, ofReal (y ^ (shape - 1))) = ofReal (z ^ shape / shape) := by
  have hi : IntegrableOn (fun y : ℝ => y ^ (shape - 1)) (Icc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hz).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_restrict_of_forall_mem measurableSet_Icc (fun y hy => rpow_nonneg hy.1 _)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
    integral_rpow (Or.inl (by linarith))]
  simp only [sub_add_cancel, zero_rpow hshape.ne', sub_zero]

private def coefficient (shape rate z : ℝ) : ℝ :=
  rate ^ shape / Gamma shape * rate * exp (-(rate * z))

private theorem coefficient_nonneg (shape rate z : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    0 ≤ coefficient shape rate z := by
  have hΓ := Gamma_pos_of_pos hshape
  unfold coefficient
  positivity

private theorem density_product (shape rate z y : ℝ) (hshape : 0 < shape) (hrate : 0 < rate)
    (hy : y ∈ Icc 0 z) :
    gammaPDF shape rate y * gammaPDF 1 rate (-y + z) =
      ofReal (coefficient shape rate z) * ofReal (y ^ (shape - 1)) := by
  have hΓ := Gamma_pos_of_pos hshape
  have hy0 : 0 ≤ y := hy.1
  have hyz : y ≤ z := hy.2
  have hfirst : 0 ≤ rate ^ shape / Gamma shape * y ^ (shape - 1) * exp (-(rate * y)) := by
    positivity
  rw [gammaPDF_of_nonneg hy.1, gammaPDF_of_nonneg (by linarith : 0 ≤ -y + z)]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]
  rw [← ENNReal.ofReal_mul hfirst,
    ← ENNReal.ofReal_mul (coefficient_nonneg shape rate z hshape hrate)]
  congr 1
  have he : exp (-(rate * y)) * exp (-(rate * (-y + z))) = exp (-(rate * z)) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = (rate ^ shape / Gamma shape * rate) *
        (exp (-(rate * y)) * exp (-(rate * (-y + z)))) * y ^ (shape - 1) := by ring
    _ = _ := by rw [he]; unfold coefficient; ring

/-- The convolution density is the gamma density with one additional shape unit. -/
theorem density_successor (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) (z : ℝ) :
    (gammaPDF shape rate ⋆ₗ[volume] gammaPDF 1 rate) z = gammaPDF (shape + 1) rate z := by
  rw [lconvolution_def]
  by_cases hz : 0 ≤ z
  · have hfun : (fun y => gammaPDF shape rate y * gammaPDF 1 rate (-y + z)) =
        (Icc 0 z).indicator (fun y =>
          ofReal (coefficient shape rate z) * ofReal (y ^ (shape - 1))) := by
      funext y
      by_cases hy : y ∈ Icc 0 z
      · simp only [indicator_of_mem hy]
        exact density_product shape rate z y hshape hrate hy
      · rw [indicator_of_notMem hy]
        rcases lt_or_ge y 0 with hy0 | hy0
        · rw [gammaPDF_of_neg hy0, zero_mul]
        · have hzy : z < y := by simp only [mem_Icc, hy0, true_and, not_le] at hy; exact hy
          rw [gammaPDF_of_neg (by linarith : -y + z < 0), mul_zero]
    rw [hfun, lintegral_indicator measurableSet_Icc,
      lintegral_const_mul _ (by fun_prop : Measurable (fun y : ℝ => ofReal (y ^ (shape - 1)))),
      power_mass shape hshape z hz, gammaPDF_of_nonneg hz,
      ← ENNReal.ofReal_mul (coefficient_nonneg shape rate z hshape hrate)]
    congr 1
    rw [Gamma_add_one hshape.ne', add_sub_cancel_right, rpow_add hrate, rpow_one]
    unfold coefficient
    field_simp
  · rw [gammaPDF_of_neg (lt_of_not_ge hz)]
    have hzero : (fun y => gammaPDF shape rate y * gammaPDF 1 rate (-y + z)) =
        fun _ => 0 := by
      funext y
      rcases lt_or_ge y 0 with hy | hy
      · rw [gammaPDF_of_neg hy, zero_mul]
      · rw [gammaPDF_of_neg (by linarith : -y + z < 0), mul_zero]
    rw [hzero, lintegral_zero]

/-- Independent gamma and exponential draws add their shapes. -/
theorem gamma_conv_exponential (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    gammaMeasure shape rate ∗ expMeasure rate = gammaMeasure (shape + 1) rate := by
  rw [expMeasure]
  change (volume.withDensity (gammaPDF shape rate)) ∗
    (volume.withDensity (gammaPDF 1 rate)) = volume.withDensity (gammaPDF (shape + 1) rate)
  rw [conv_withDensity_eq_lconvolution (measurable_pdf shape rate) (measurable_pdf 1 rate)]
  congr 1
  funext z
  exact density_successor shape rate hshape hrate z

/-- The source's exponential-first ordering has the same sum law. -/
theorem exponential_conv_gamma (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    expMeasure rate ∗ gammaMeasure shape rate = gammaMeasure (shape + 1) rate := by
  let := isProbabilityMeasure_gammaMeasure hshape hrate
  let := isProbabilityMeasure_expMeasure hrate
  rw [Measure.conv_comm, gamma_conv_exponential shape rate hshape hrate]

/-- Arbitrary ENNReal credits for the sum are preserved, with no finiteness restriction. -/
theorem expectation (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, F (x + y) ∂expMeasure rate ∂gammaMeasure shape rate) =
      ∫⁻ z, F z ∂gammaMeasure (shape + 1) rate := by
  let := isProbabilityMeasure_gammaMeasure hshape hrate
  let := isProbabilityMeasure_expMeasure hrate
  rw [← Measure.lintegral_conv hF, gamma_conv_exponential shape rate hshape hrate]

end

end SampLib.GammaSuccessor
