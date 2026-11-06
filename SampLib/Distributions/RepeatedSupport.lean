import SampLib.Samplers.SampleWithReplacement

/-! Almost-sure coordinate properties of independent finite repetitions. -/

open MeasureTheory

namespace SampLib.SampleWithReplacement

noncomputable section

variable {α : Type _} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- An almost-sure property of one draw holds at every sampled coordinate. -/
theorem all_ae (μ : Measure α) [IsProbabilityMeasure μ] (P : α → Prop)
    (hP : ∀ᵐ x ∂μ, P x) (n : ℕ) :
    ∀ᵐ xs ∂law μ n, ∀ i, P (xs i) := by
  induction n with
  | zero => simp [law]
  | succ n IH =>
    rw [law, ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable _).measurableSet]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
    filter_upwards [hP] with x hx
    filter_upwards [IH] with xs hxs
    intro i
    exact Fin.cases hx hxs i

end

end SampLib.SampleWithReplacement
