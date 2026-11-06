import SampLib.Common.Laws.ListProduct

/-! Support of independent finite coordinate lists. -/

open MeasureTheory

namespace SampLib.ListProduct

noncomputable section

variable {α : Type _} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem length_ae (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i n : ℕ) :
    ∀ᵐ xs ∂law μ i n, xs.length = n := by
  induction n generalizing i with
  | zero => simp [law]
  | succ n IH =>
    rw [law, ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable _).measurableSet]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
    filter_upwards [IH (i + 1)] with xs hxs
    exact Filter.Eventually.of_forall fun x => by simp [hxs]

end

end SampLib.ListProduct
