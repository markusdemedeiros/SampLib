module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! # Vanishing uncertainty in shared latent comparisons

Distinct latent values eventually separate as the measurable observation errors
vanish. Finite measure then supplies a global finite horizon with arbitrarily
small unresolved mass; no uniform conditional retry bound is required.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SampLib.LatentComparisonUncertainty

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Points at which the current total error can still hide the order of two values. -/
def band (left right : Ω → ℝ) (error : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {x | |left x - right x| ≤ error n x}

theorem measurableSet_band {left right : Ω → ℝ} {error : ℕ → Ω → ℝ}
    (hl : Measurable left) (hr : Measurable right) (he : ∀ n, Measurable (error n)) (n : ℕ) :
    MeasurableSet (band left right error n) :=
  measurableSet_le (hl.sub hr).abs (he n)

/-- Dominated convergence turns pointwise separation into vanishing unresolved mass. -/
theorem mass_tendsto_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    {left right : Ω → ℝ} {error : ℕ → Ω → ℝ}
    (hl : Measurable left) (hr : Measurable right) (he : ∀ n, Measurable (error n))
    (herror : ∀ᵐ x ∂μ, Tendsto (fun n => error n x) atTop (𝓝 0))
    (hne : ∀ᵐ x ∂μ, left x ≠ right x) :
    Tendsto (fun n => μ (band left right error n)) atTop (𝓝 0) := by
  have hband := measurableSet_band hl hr he
  have hmeas (n : ℕ) : Measurable ((band left right error n).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hband n)
  have hbound (n : ℕ) :
      (band left right error n).indicator (fun _ => (1 : ℝ≥0∞)) ≤ᵐ[μ] fun _ => 1 := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ band left right error n <;> simp [hx]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n =>
      (band left right error n).indicator (fun _ => (1 : ℝ≥0∞)) x) atTop (𝓝 0) := by
    filter_upwards [herror, hne] with x hx hneq
    have hd : 0 < |left x - right x| := abs_pos.mpr (sub_ne_zero.mpr hneq)
    have hevent := hx.eventually_lt_const hd
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    simp [band, not_le.mpr hn]
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    hmeas hbound (by simp) hlim
  simpa only [lintegral_indicator_const (hband _), one_mul, lintegral_zero] using h

/-- The finite-horizon proof may choose one unresolved band below its error allowance. -/
theorem exists_small_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    {left right : Ω → ℝ} {error : ℕ → Ω → ℝ}
    (hl : Measurable left) (hr : Measurable right) (he : ∀ n, Measurable (error n))
    (herror : ∀ᵐ x ∂μ, Tendsto (fun n => error n x) atTop (𝓝 0))
    (hne : ∀ᵐ x ∂μ, left x ≠ right x) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n, μ (band left right error n) < δ := by
  exact ((mass_tendsto_zero μ hl hr he herror hne).eventually_lt_const hδ).exists

/-- A horizon can be chosen after any already requested precision. -/
theorem exists_small_mass_ge (μ : Measure Ω) [IsFiniteMeasure μ]
    {left right : Ω → ℝ} {error : ℕ → Ω → ℝ}
    (hl : Measurable left) (hr : Measurable right) (he : ∀ n, Measurable (error n))
    (herror : ∀ᵐ x ∂μ, Tendsto (fun n => error n x) atTop (𝓝 0))
    (hne : ∀ᵐ x ∂μ, left x ≠ right x) (start : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n, start ≤ n ∧ μ (band left right error n) < δ := by
  exact ((eventually_ge_atTop start).and
    ((mass_tendsto_zero μ hl hr he herror hne).eventually_lt_const hδ)).exists

end SampLib.LatentComparisonUncertainty
