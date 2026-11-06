module

public import Mathlib.Probability.Distributions.Gamma

@[expose] public section

/-! # Gamma-mixture credits for lazy Lindley sampling

The mixture is stated for mathematical latent values. Its interpretation does not
require the interval oracles to expose those values eagerly.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.PSRNGammaMixtures

noncomputable section

/-- Shape-mixture law at a common rate, with the first component selected by `p`. -/
def law (p : unitInterval) (a b rate : ℝ) : Measure ℝ :=
  (ENNReal.ofReal p • gammaMeasure a rate) +
    (ENNReal.ofReal (1 - p) • gammaMeasure b rate)

theorem isProbabilityMeasure_law (p : unitInterval) {a b rate : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < rate) : IsProbabilityMeasure (law p a b rate) := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  have := isProbabilityMeasure_gammaMeasure hb hr
  refine ⟨?_⟩
  simp [law, ← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]

/-- Selection transfers the expectation of the chosen latent component without
any boundedness or finiteness condition on the continuation credit. -/
theorem expectation_preservation (p : unitInterval) (a b rate : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F x ∂law p a b rate =
      ENNReal.ofReal p * (∫⁻ x, F x ∂gammaMeasure a rate) +
      ENNReal.ofReal (1 - p) * (∫⁻ x, F x ∂gammaMeasure b rate) := by
  simp [law, smul_eq_mul]

/-- The mixture law has the corresponding weighted sum of the gamma densities. -/
theorem law_eq_withDensity (p : unitInterval) (a b rate : ℝ) :
    law p a b rate = volume.withDensity (fun x =>
      ENNReal.ofReal p * gammaPDF a rate x +
      ENNReal.ofReal (1 - p) * gammaPDF b rate x) := by
  have ha : Measurable (gammaPDF a rate) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a rate)
  have hb : Measurable (gammaPDF b rate) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal b rate)
  change _ = volume.withDensity
    ((ENNReal.ofReal p • gammaPDF a rate) + (ENNReal.ofReal (1 - p) • gammaPDF b rate))
  rw [withDensity_add_left (ha.const_smul _),
    withDensity_smul _ ha, withDensity_smul _ hb]
  rfl

/-- Lindley's mixture weight for rate `rate > 0`. -/
def lindleyWeight (rate : ℝ) (hr : 0 < rate) : unitInterval :=
  ⟨rate / (rate + 1), (div_nonneg hr.le (by positivity)),
    (div_le_one (by positivity)).mpr (by linarith)⟩

/-- Lindley density obtained by mixing shapes one and two. -/
def lindleyPDFReal (rate x : ℝ) : ℝ :=
  if 0 ≤ x then rate ^ 2 / (rate + 1) * (1 + x) * Real.exp (-(rate * x)) else 0

/-- The shape mixture gives the familiar Lindley density, rather than merely an
unnamed mixture of gamma distributions. -/
theorem lindley_density (rate : ℝ) (hr : 0 < rate) (x : ℝ) :
    rate / (rate + 1) * gammaPDFReal 1 rate x +
      (1 - rate / (rate + 1)) * gammaPDFReal 2 rate x = lindleyPDFReal rate x := by
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, lindleyPDFReal, ite_eq_left hx, Real.Gamma_one,
      show Real.Gamma 2 = 1 by simp,
      div_one, sub_self, Real.rpow_zero, mul_one, Real.rpow_one,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_two]
    field_simp
    ring
  · simp [gammaPDFReal, lindleyPDFReal, hx]

/-- The positive-rate Lindley mixture has exactly its standard density. -/
theorem lindley_law_eq_withDensity (rate : ℝ) (hr : 0 < rate) :
    law (lindleyWeight rate hr) 1 2 rate =
      volume.withDensity (fun x => ENNReal.ofReal (lindleyPDFReal rate x)) := by
  rw [law_eq_withDensity]
  congr 1
  funext x
  have hp := (lindleyWeight rate hr).2.1
  have hq := sub_nonneg.mpr (lindleyWeight rate hr).2.2
  rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hq,
    ← ENNReal.ofReal_add
      (mul_nonneg hp (gammaPDFReal_nonneg (by norm_num) hr x))
      (mul_nonneg hq (gammaPDFReal_nonneg (by norm_num) hr x))]
  exact congrArg ENNReal.ofReal (lindley_density rate hr x)

/-- Normalization of Lindley's density follows from the normalized shape mixture. -/
theorem lintegral_lindleyPDFReal (rate : ℝ) (hr : 0 < rate) :
    ∫⁻ x, ENNReal.ofReal (lindleyPDFReal rate x) = 1 := by
  have := isProbabilityMeasure_law (a := 1) (b := 2)
    (lindleyWeight rate hr) (by norm_num) (by norm_num) hr
  have h := measure_univ (μ := law (lindleyWeight rate hr) 1 2 rate)
  rwa [lindley_law_eq_withDensity rate hr, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

end

end SampLib.PSRNGammaMixtures
