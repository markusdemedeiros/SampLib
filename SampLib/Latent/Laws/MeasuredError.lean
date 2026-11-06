module

public import SampLib.Latent.Laws.SameWorld
public import SampLib.Latent.Laws.ComparisonUncertainty

@[expose] public section

/-! # Measurable uncertainty envelopes for deferred comparisons

Measurability is an additional comparison requirement, not an alteration of the
basic oracle protocol. Vanishing band mass gives a global finite proof horizon.
-/

open MeasureTheory
open Filter Topology
open scoped ENNReal

namespace SampLib.LatentReal.Model

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The observation-error envelope is measurable at every requested precision. -/
def MeasurableError (D : Model Ω S) : Prop := ∀ n, Measurable (D.error n)

/-- Overlapping enclosures can hide the order only inside this latent band. -/
def comparisonBand (left right : Model Ω S) (n : ℕ) : Set Ω :=
  LatentComparisonUncertainty.band left.value right.value
    (fun k x => left.error k x + right.error k x) n

theorem measurableSet_comparisonBand (left right : Model Ω S)
    (hl : left.MeasurableError) (hr : right.MeasurableError) (n : ℕ) :
    MeasurableSet (comparisonBand left right n) :=
  LatentComparisonUncertainty.measurableSet_band left.measurable_value right.measurable_value
    (fun k => (hl k).add (hr k)) n

/-- Both error envelopes vanish under any posterior of their common world. -/
theorem SameWorld.sum_error_tendsto {left right : Model Ω S} (h : SameWorld left right) (s : S) :
    ∀ᵐ x ∂left.posterior s,
      Tendsto (fun n => left.error n x + right.error n x) atTop (𝓝 0) := by
  have hr := right.error_tendsto s
  rw [h.posterior_eq s] at hr
  filter_upwards [left.error_tendsto s, hr] with x hx hy
  simpa only [add_zero] using hx.add hy

/-- A proof may stop at a single fixed later horizon; no monotone error schedule is needed. -/
theorem SameWorld.exists_small_comparison_band {left right : Model Ω S}
    (h : SameWorld left right) (hl : left.MeasurableError) (hr : right.MeasurableError)
    (s : S) (hne : ∀ᵐ x ∂left.posterior s, left.value x ≠ right.value x)
    (start : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n, start ≤ n ∧ left.posterior s (comparisonBand left right n) < δ :=
  LatentComparisonUncertainty.exists_small_mass_ge (left.posterior s)
    left.measurable_value right.measurable_value (fun n => (hl n).add (hr n))
    (h.sum_error_tendsto s) hne start hδ

end

end SampLib.LatentReal.Model
