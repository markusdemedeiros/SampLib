import SampLib.Combinatorial.Laws.Choice
import SampLib.Discrete.Laws.WeightedChoice

/-! # Classified mixture law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ClassifiedModel

noncomputable section

theorem length_ne_zero (weights : List ℕ) [NeZero weights.sum] :
    weights.length ≠ 0 := by
  intro h
  have hz : weights = [] := List.eq_nil_of_length_eq_zero h
  simpa [hz] using NeZero.ne weights.sum

/-- Totalize the category index; the modular fallback is outside weighted support. -/
def position (weights : List ℕ) [NeZero weights.sum] (i : ℕ) : Fin weights.length :=
  letI : NeZero weights.length := ⟨length_ne_zero weights⟩
  Choice.position weights.length i

theorem position_of_lt (weights : List ℕ) [NeZero weights.sum]
    (i : ℕ) (hi : i < weights.length) : position weights i = ⟨i, hi⟩ := by
  let : NeZero weights.length := ⟨length_ne_zero weights⟩
  exact Choice.position_of_lt i hi

variable {α : Type _} [MeasurableSpace α]

/-- Keep the sampled class alongside its independent class-conditional observation. -/
def law (weights : List ℕ) [NeZero weights.sum] (μ : Fin weights.length → Measure α) :
    Measure (Fin weights.length × α) :=
  (WeightedChoice.law weights).bind
    (fun i => (μ (position weights i)).map (fun x => (position weights i, x)))

instance (weights : List ℕ) [NeZero weights.sum] (μ : Fin weights.length → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (law weights μ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the class gives the tagged mixture expectation. -/
theorem expectation (weights : List ℕ) [NeZero weights.sum]
    (μ : Fin weights.length → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (F : Fin weights.length × α → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ i, ∫⁻ x, F (position weights i, x) ∂μ (position weights i)
      ∂WeightedChoice.law weights = ∫⁻ p, F p ∂law weights μ := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
  apply lintegral_congr
  intro i
  have hm : Measurable (fun x : α => (position weights i, x)) :=
    measurable_const.prodMk measurable_id
  rw [lintegral_map hF hm]

end

end SampLib.ClassifiedModel
