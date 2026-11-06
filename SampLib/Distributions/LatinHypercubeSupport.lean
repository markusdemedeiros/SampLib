import SampLib.Samplers.LatinHypercube1D
import SampLib.Distributions.ListProductSupport

/-! Fixed column lengths in shuffled stratification. -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatinHypercube1D

noncomputable section

/-- Permuting positions preserves the number of strata. -/
theorem length_ae (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    ∀ᵐ xs ∂law scale strata hs h, xs.length = strata := by
  rw [ae_iff, law, Measure.bind_apply (Set.to_countable _).measurableSet
    (measurable_of_countable _).aemeasurable]
  have hlen : ∀ᵐ xs ∂Stratified1D.law scale strata hs h, xs.length = strata :=
    ListProduct.length_ae _ 0 strata
  calc
    _ = ∫⁻ _ : List ℤ, (0 : ℝ≥0∞) ∂Stratified1D.law scale strata hs h := by
      apply lintegral_congr_ae
      filter_upwards [hlen] with xs hxs
      rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      have hp : Shuffle.output xs ⁻¹' {ys | ¬ys.length = strata} = ∅ := by
        ext σ
        simp [Shuffle.output, hxs]
      rw [hp, measure_empty]
    _ = 0 := by simp

end

end SampLib.LatinHypercube1D
