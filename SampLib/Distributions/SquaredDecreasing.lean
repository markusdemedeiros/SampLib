module

public import SampLib.Distributions.MaximumUniform

@[expose] public section

/-! # Squared-exponential parity for maximum-uniform chains

The maximum of two uniforms has density `2t`. Integrating
`2t exp(-t²)` gives the parity-reversal probability `1-exp(-x²)`.
-/

open Set MeasureTheory Real ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.SquaredDecreasing

noncomputable section

def decay (x : ℝ) : unitInterval :=
  ⟨exp (-x ^ 2), (exp_pos _).le, exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))⟩

theorem measurable_decay : Measurable decay :=
  (by fun_prop : Measurable (fun x : ℝ => exp (-x ^ 2))).subtype_mk

def flipBias (x y : ℝ) : unitInterval := if y < x then decay y else 0

theorem measurable_flipBias (x : ℝ) : Measurable (flipBias x) :=
  Measurable.ite measurableSet_Iio measurable_decay measurable_const

theorem integral_two_mul_exp_neg_sq (x : ℝ) :
    ∫ y in (0 : ℝ)..x, 2 * y * exp (-y ^ 2) = 1 - exp (-x ^ 2) := by
  have hd (y : ℝ) : HasDerivAt (fun z => -exp (-z ^ 2))
      (2 * y * exp (-y ^ 2)) y := by
    convert (((hasDerivAt_id y).pow 2).neg.exp).neg using 1 <;>
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    · rfl
    · ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (Continuous.intervalIntegrable (by fun_prop) 0 x)
  simpa only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, exp_zero, sub_neg_eq_add,
    sub_eq_add_neg, neg_neg, add_comm] using h

private theorem lower_window (x : ℝ) (hx : x ≤ 1) :
    Iio x ∩ Icc (0 : ℝ) 1 = Ico 0 x := by
  ext y
  simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le.trans hx⟩⟩

/-- The probability of changing parity after the first maximum-uniform draw. -/
theorem flip_mass (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, ofReal (flipBias x y : ℝ) ∂MaximumUniform.law 1 =
      ofReal (1 - (decay x : ℝ)) := by
  rw [MaximumUniform.law, lintegral_withDensity_eq_lintegral_mul _
    (MaximumUniform.measurable_density 1)
    (show Measurable (fun y => ofReal (flipBias x y : ℝ)) from
      ENNReal.measurable_ofReal.comp ((measurable_flipBias x).subtype_val))]
  have hfun : (fun y => MaximumUniform.density 1 y * ofReal (flipBias x y : ℝ)) =
      (Iio x).indicator (fun y => MaximumUniform.density 1 y * ofReal (decay y : ℝ)) := by
    funext y
    by_cases h : y < x <;> simp [flipBias, h]
  change (∫⁻ y, MaximumUniform.density 1 y * ofReal (flipBias x y : ℝ) ∂unifUnit) = _
  rw [hfun]
  change (∫⁻ y, _ ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [ProbLang.TotalEris.Examples.lintegral_indicator_restrict measurableSet_Iio,
    lower_window x hx.2, restrict_Ico_eq_restrict_Icc]
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) x) :
      MaximumUniform.density 1 y * ofReal (decay y : ℝ) =
        ofReal (2 * y * exp (-y ^ 2)) := by
    simp only [MaximumUniform.density, Nat.cast_add, Nat.cast_one, pow_one, decay]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hy.1)]
    norm_num
  rw [setLIntegral_congr_fun measurableSet_Icc hpoint,
    ProbLang.TotalEris.Examples.lintegral_ofReal_Icc hx.1 (by fun_prop)
      (fun y hy => mul_nonneg (mul_nonneg (by norm_num) hy.1) (exp_pos _).le),
    integral_two_mul_exp_neg_sq]
  rfl

/-- The continuation event has probability `x²`. -/
theorem continuation_mass (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∫⁻ y, (if y < x then (1 : ℝ≥0∞) else 0) ∂MaximumUniform.law 1 = ofReal (x ^ 2) := by
  have hfun : (fun y : ℝ => if y < x then (1 : ℝ≥0∞) else 0) =
      (Iio x).indicator (fun _ => 1) := rfl
  rw [hfun, lintegral_indicator measurableSet_Iio, setLIntegral_const, one_mul,
    measure_congr (Iio_ae_eq_Iic (μ := MaximumUniform.law 1)),
    MaximumUniform.law_apply_Iic, MaximumUniform.unit_apply_Iic,
    min_eq_left hx.2, ← ENNReal.ofReal_pow hx.1]

end

end SampLib.SquaredDecreasing
