module

public import SampLib.Distributions.ExponentialDigits
public import SampLib.Distributions.Exponential
public import SampLib.Distributions.Geometric

@[expose] public section

/-! # Joining the exponential whole and fractional parts

Geometric strip weights cancel the fractional law's normalizer. Translating
successive unit strips then recovers the exponential density, for arbitrary
nonnegative continuation functions, including infinite ones.
-/

open Set MeasureTheory Real ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ExponentialDigits

noncomputable section

/-- The geometric stopping coin for the integer part. -/
def wholeBias (rate : ℝ) (hrate : 0 < rate) : unitInterval :=
  ⟨1 - exp (-rate), (normalizer_pos rate hrate).le, by linarith [exp_pos (-rate)]⟩

theorem wholeBias_pos (rate : ℝ) (hrate : 0 < rate) :
    0 < (wholeBias rate hrate : ℝ) := normalizer_pos rate hrate

/-- The fractional law integrates its normalized restricted density. -/
theorem lintegral_fraction (rate : ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, H x ∂fraction rate) = (ofReal (1 - exp (-rate)))⁻¹ *
      ∫⁻ x in Ico 0 1, density rate x * H x := by
  rw [fraction, lintegral_smul_measure, restrict_withDensity measurableSet_Ico,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density rate) hH]
  rfl

private theorem strip_factor (rate : ℝ) (hrate : 0 < rate) (n : ℕ) (x : ℝ) :
    ofReal ((1 - (wholeBias rate hrate : ℝ)) ^ n * (wholeBias rate hrate : ℝ)) *
      (ofReal (1 - exp (-rate)))⁻¹ * density rate x = density rate ((n : ℝ) + x) := by
  have hnorm : ofReal (1 - exp (-rate)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (normalizer_pos rate hrate))
  have hExp : exp (-rate) ^ n * exp (-(rate * x)) = exp (-(rate * ((n : ℝ) + x))) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    ring
  simp only [wholeBias, sub_sub_cancel]
  rw [ENNReal.ofReal_mul (pow_nonneg (exp_pos (-rate)).le n)]
  have hcancel : ofReal (exp (-rate) ^ n) * ofReal (1 - exp (-rate)) *
      (ofReal (1 - exp (-rate)))⁻¹ = ofReal (exp (-rate) ^ n) := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hnorm ENNReal.ofReal_ne_top, mul_one]
  rw [hcancel]
  unfold density
  rw [← ENNReal.ofReal_mul (pow_nonneg (exp_pos (-rate)).le n)]
  congr 1
  calc
    _ = rate * (exp (-rate) ^ n * exp (-(rate * x))) := by ring
    _ = _ := by rw [hExp]

/-- The usual exponential law has its defining density on the nonnegative half-line. -/
theorem lintegral_exponential (rate : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂expMeasure rate) = ∫⁻ z in Ici 0, density rate z * F z := by
  have hm : Measurable (gammaPDF 1 rate) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 rate)
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hm hF]
  change (∫⁻ z, exponentialPDF rate z * F z) = _
  have hpdf : (fun z => exponentialPDF rate z * F z) =
      (Ici (0 : ℝ)).indicator (fun z => density rate z * F z) := by
    funext z
    by_cases hz : 0 ≤ z
    · simp [exponentialPDF_of_nonneg hz, density, hz]
    · simp [exponentialPDF_of_neg (lt_of_not_ge hz), hz]
  rw [hpdf, lintegral_indicator measurableSet_Ici]

/-- Independent geometric whole and truncated-exponential fraction give `Exp(rate)`. -/
theorem expectation (rate : ℝ) (hrate : 0 < rate) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ n, ∫⁻ x, F ((n : ℝ) + x) ∂fraction rate
      ∂geometricMeasure (wholeBias rate hrate)) = ∫⁻ z, F z ∂expMeasure rate := by
  have hstop : wholeBias rate hrate ≠ 0 := by
    intro h
    have hpos := wholeBias_pos rate hrate
    simp only [h, Set.Icc.coe_zero, lt_self_iff_false] at hpos
  rw [geometricMeasure_eq hstop]
  simp only [lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [lintegral_exponential rate F hF, Distributions.Exponential.lintegral_Ici_eq_tsum]
  apply tsum_congr
  intro n
  have hFn : Measurable (fun x : ℝ => F ((n : ℝ) + x)) := by fun_prop
  rw [lintegral_fraction rate _ hFn, ← mul_assoc]
  have hK : Measurable (fun x : ℝ => density rate x * F ((n : ℝ) + x)) := by fun_prop
  rw [← lintegral_const_mul _ hK]
  apply setLIntegral_congr_fun measurableSet_Ico
  intro x _
  dsimp only
  rw [← mul_assoc, strip_factor]

end

end SampLib.ExponentialDigits
