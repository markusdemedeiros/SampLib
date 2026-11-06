module

public import SampLib.Distributions.DyadicPosterior
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

@[expose] public section

/-! # Refinement of cached dyadic posteriors

Every refinement preserves the parent posterior's null sets. Comparison facts
learned before another read therefore remain valid afterward.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.DyadicPosterior

noncomputable section

private theorem half_absolutelyContinuous (b : Bool) : unitLaw.map (half b) ≪ unitLaw := by
  intro s hs
  rw [unit_split, Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hs
  have hzero : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
  simp only [smul_eq_mul, add_eq_zero, mul_eq_zero, hzero, false_or] at hs
  cases b
  · exact hs.1
  · exact hs.2

/-- Every finite cached posterior is absolutely continuous with the original uniform. -/
theorem law_absolutelyContinuous_unit (p : List Bool) : law p ≪ unitLaw := by
  induction p with
  | nil => exact law_nil.absolutelyContinuous
  | cons b p IH =>
    rw [law_cons]
    exact (IH.map (measurable_half b)).trans (half_absolutelyContinuous b)

/-- Extending the cached prefix preserves every previously known almost-everywhere fact. -/
theorem law_refines {p q : List Bool} (hp : p <+: q) : law q ≪ law p := by
  rcases hp with ⟨r, rfl⟩
  rw [law_append, law]
  exact (law_absolutelyContinuous_unit r).map (measurable_embed p)

theorem resolves_refines {p q : List Bool} (hp : p <+: q) {t : ℝ} {b : Bool}
    (h : resolves p t b) : resolves q t b := (law_refines hp).ae_le h

end

end SampLib.DyadicPosterior
