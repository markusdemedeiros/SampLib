module

public import SampLib.Distributions.PSRNGammaMixtures

@[expose] public section

/-! # Densities for the lazy gamma-mixture families

The three component pairs below cover Garima, i-Garima, weighted
exponential-gamma, xgamma and Mirra. Their selector credit is shared with the
underlying gamma-mixture sampler; only the density identification changes.
-/

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.PSRNDistributionMixtures

noncomputable section

/-- The density of a gamma mixture, with the same selector as the program. -/
def density (p : unitInterval) (a b rate : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ofReal (p : ℝ) * gammaPDF a rate x +
    ofReal (1 - (p : ℝ)) * gammaPDF b rate x

theorem measurable_density (p : unitInterval) (a b rate : ℝ) :
    Measurable (density p a b rate) := by
  unfold density gammaPDF
  fun_prop

/-- Deterministic transformations act on each component of the same mixture. -/
theorem map_law {β : Type*} [MeasurableSpace β] (p : unitInterval)
    (a b rate : ℝ) {f : ℝ → β} (hf : Measurable f) :
    (PSRNGammaMixtures.law p a b rate).map f =
      (ofReal (p : ℝ) • (gammaMeasure a rate).map f) +
        (ofReal (1 - (p : ℝ)) • (gammaMeasure b rate).map f) := by
  simp only [PSRNGammaMixtures.law, Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable]

private theorem gamma_one {rate x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal 1 rate x = rate * Real.exp (-(rate * x)) := by
  simp [gammaPDFReal, hx]

private theorem gamma_two {rate x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal 2 rate x = rate ^ 2 * x * Real.exp (-(rate * x)) := by
  simp only [gammaPDFReal, ite_eq_left hx,
    show Real.Gamma 2 = 1 by simp,
    div_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]

private theorem gamma_three {rate x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal 3 rate x = rate ^ 3 / 2 * x ^ 2 * Real.exp (-(rate * x)) := by
  simp only [gammaPDFReal, ite_eq_left hx,
    show Real.Gamma 3 = 2 by simp,
    show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]

/-- The shape-one/two mixture underlying Garima and i-Garima. -/
theorem density_one_two (p : unitInterval) {rate x : ℝ} (hr : 0 < rate)
    (hx : 0 ≤ x) :
    density p 1 2 rate x =
      ofReal (rate * ((p : ℝ) + (1 - (p : ℝ)) * rate * x) *
        Real.exp (-(rate * x))) := by
  have ha := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 1) hr x
  have hb := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 2) hr x
  rw [density, gammaPDF, gammaPDF, ← ENNReal.ofReal_mul p.2.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2), ← ENNReal.ofReal_add (mul_nonneg p.2.1 ha)
      (mul_nonneg (sub_nonneg.mpr p.2.2) hb), gamma_one hx, gamma_two hx]
  congr 1
  ring

/-- The shape-one/three mixture underlying xgamma and Mirra. -/
theorem density_one_three (p : unitInterval) {rate x : ℝ} (hr : 0 < rate)
    (hx : 0 ≤ x) :
    density p 1 3 rate x =
      ofReal (rate * ((p : ℝ) + (1 - (p : ℝ)) * rate ^ 2 * x ^ 2 / 2) *
        Real.exp (-(rate * x))) := by
  have ha := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 1) hr x
  have hb := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 3) hr x
  rw [density, gammaPDF, gammaPDF, ← ENNReal.ofReal_mul p.2.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2), ← ENNReal.ofReal_add (mul_nonneg p.2.1 ha)
      (mul_nonneg (sub_nonneg.mpr p.2.2) hb), gamma_one hx, gamma_three hx]
  congr 1
  ring

/-- The shape-two/three mixture underlying the weighted exponential-gamma law. -/
theorem density_two_three (p : unitInterval) {rate x : ℝ} (hr : 0 < rate)
    (hx : 0 ≤ x) :
    density p 2 3 rate x =
      ofReal (rate ^ 2 * x * ((p : ℝ) + (1 - (p : ℝ)) * rate * x / 2) *
        Real.exp (-(rate * x))) := by
  have ha := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 2) hr x
  have hb := gammaPDFReal_nonneg (by norm_num : (0 : ℝ) < 3) hr x
  rw [density, gammaPDF, gammaPDF, ← ENNReal.ofReal_mul p.2.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2), ← ENNReal.ofReal_add (mul_nonneg p.2.1 ha)
      (mul_nonneg (sub_nonneg.mpr p.2.2) hb), gamma_two hx, gamma_three hx]
  congr 1
  ring

end

end SampLib.PSRNDistributionMixtures
