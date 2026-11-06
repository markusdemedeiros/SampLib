module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The acceptance identity for lazy beta rejection

The two coin calls share their proposed uniform value. Their conditional success
probabilities multiply pointwise; integrating that product gives the beta law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SampLib.PSRNBetaRejection

noncomputable section

/-- The unnormalized beta acceptance weight, supported on the open unit interval. -/
def weight (a b x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then x ^ (a - 1) * (1 - x) ^ (b - 1) else 0

theorem weight_eq_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    weight a b x = beta a b * betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [weight, betaPDFReal, ite_eq_left hx]
    field_simp [ne_of_gt (beta_pos ha hb)]
  · simp [weight, betaPDFReal, hx]

theorem weight_mem {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (x : ℝ) :
    weight a b x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [weight, ite_eq_left hx, mem_Icc]
    have hleft : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hx.1.le _
    have hright : 0 ≤ (1 - x) ^ (b - 1) :=
      Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _
    refine ⟨mul_nonneg hleft hright, ?_⟩
    simpa only [mul_one] using mul_le_mul
      (Real.rpow_le_one hx.1.le hx.2.le (sub_nonneg.mpr ha))
      (Real.rpow_le_one (sub_nonneg.mpr hx.2.le) (by linarith) (sub_nonneg.mpr hb))
      hright zero_le_one
  · simp [weight, hx]

/-- A successful proposal carries precisely beta-distributed output credit.
The identity admits infinite credits and does not replace the shared proposal
by independent marginal coins. -/
theorem acceptance_expectation {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, ENNReal.ofReal (weight a b x) * F x =
      ENNReal.ofReal (beta a b) * ∫⁻ x, F x ∂betaMeasure a b := by
  have hpdf : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdf hF]
  simp_rw [weight_eq_betaPDFReal ha hb, ENNReal.ofReal_mul (beta_pos ha hb).le,
    mul_assoc]
  exact lintegral_const_mul _ (hpdf.mul hF)

/-- Positive beta normalization is exactly the rejection acceptance probability. -/
theorem acceptance_mass {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, ENNReal.ofReal (weight a b x) = ENNReal.ofReal (beta a b) := by
  have := isProbabilityMeasureBeta ha hb
  simpa only [mul_one, lintegral_one, measure_univ] using
    (acceptance_expectation ha hb (fun _ => 1) measurable_const)

end

end SampLib.PSRNBetaRejection
