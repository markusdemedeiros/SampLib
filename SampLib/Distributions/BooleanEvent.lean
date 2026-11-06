import SampLib.Distributions.BernoulliMixture

/-! A measurable event in a probability space is a Bernoulli observation. -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.BooleanEvent

noncomputable section

variable {α : Type _} [MeasurableSpace α]

/-- The probability of a Boolean event, as a unit-interval bias. -/
def bias (μ : Measure α) [IsProbabilityMeasure μ] (event : α → Bool) : unitInterval :=
  ⟨μ.real (event ⁻¹' {true}), measureReal_nonneg, measureReal_le_one⟩

/-- Normalization identifies both event outcomes, including probabilities zero and one. -/
theorem map_eq (μ : Measure α) [IsProbabilityMeasure μ] (event : α → Bool)
    (hevent : Measurable event) : μ.map event = RealCoin.law (bias μ event) := by
  let : IsProbabilityMeasure (μ.map event) := ⟨by
    rw [Measure.map_apply hevent MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ]⟩
  apply BernoulliMixture.eq_bernoulli_of_apply_true
  rw [Measure.map_apply hevent (measurableSet_singleton true)]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- The event abstraction preserves arbitrary nonnegative extended-real credits. -/
theorem expectation (μ : Measure α) [IsProbabilityMeasure μ] (event : α → Bool)
    (hevent : Measurable event) (F : Bool → ℝ≥0∞) :
    ∫⁻ x, F (event x) ∂μ = ∫⁻ b, F b ∂RealCoin.law (bias μ event) := by
  rw [← map_eq μ event hevent,
    lintegral_map (measurable_of_countable _) hevent]

end

end SampLib.BooleanEvent
