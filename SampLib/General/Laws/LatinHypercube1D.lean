import SampLib.Combinatorial.Laws.Shuffle
import SampLib.General.Laws.ListProductSupport
import SampLib.General.Laws.Stratified1D

/-! # Shuffled stratification law

Independent stratum jitter followed by a uniform permutation of positions. The bins use
rounded integer boundaries, so the marginal on the whole grid need not be uniform when the
bin widths differ.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatinHypercube1D

noncomputable section

/-- Independent stratum jitter followed by an independent uniform position permutation. -/
def law (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) : Measure (List ℤ) :=
  (Stratified1D.law scale strata hs h).bind
    (fun xs => (Shuffle.law xs).map (Shuffle.output xs))

instance (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    IsProbabilityMeasure (law scale strata hs h) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the jittered points leaves the uniform permutation expectation. -/
theorem expectation (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale)
    (F : List ℤ → ℝ≥0∞) :
    ∫⁻ xs, ∫⁻ σ, F (Shuffle.output xs σ) ∂Shuffle.law xs
        ∂Stratified1D.law scale strata hs h = ∫⁻ ys, F ys ∂law scale strata hs h := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr
  intro xs
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

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
