module

public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! # Finite dependent-product posteriors

One coordinate is disintegrated while all remaining coordinates and their joint
continuation credit stay intact. Coordinatewise refinement preserves null sets.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FiniteProductPosterior

noncomputable section

/-- Reassemble one chosen coordinate and its complement in their original order. -/
def join {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) :
    (α i × (∀ j : Fin n, α (i.succAbove j))) ≃ᵐ (∀ j, α j) :=
  (MeasurableEquiv.piFinSuccAbove α i).symm

theorem pi_eq_map_split {n : ℕ} (α : Fin (n + 1) → Type*)
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n + 1)) :
    Measure.pi μ = ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))).map (join α i) := by
  simpa only [join] using ((measurePreserving_piFinSuccAbove μ i).symm _).map_eq.symm

/-- Refining every component cannot introduce mass on a joint null event. -/
theorem absolutelyContinuous {n : ℕ} (α : Fin n → Type*) [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
    have heq : μ = ν := funext fun i => i.elim0
    rw [heq]
  | succ n ih =>
    rw [pi_eq_map_split α μ 0, pi_eq_map_split α ν 0]
    apply Measure.AbsolutelyContinuous.map _ (join α 0).measurable
    exact (h 0).prod (ih (fun j => α ((0 : Fin (n + 1)).succAbove j))
      (fun j => μ ((0 : Fin (n + 1)).succAbove j))
      (fun j => ν ((0 : Fin (n + 1)).succAbove j))
      (fun j => h ((0 : Fin (n + 1)).succAbove j)))

/-- The conditional credit of a single coordinate includes the entire remaining world. -/
def coordinateCredit {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) (i : Fin (n + 1))
    (F : (∀ j, α j) → ℝ≥0∞) (x : α i) : ℝ≥0∞ :=
  ∫⁻ others, F (join α i (x, others)) ∂Measure.pi (fun j => μ (i.succAbove j))

theorem measurable_coordinateCredit {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1))
    {F : (∀ j, α j) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (coordinateCredit μ i F) :=
  (hF.comp (join α i).measurable).lintegral_prod_right'

theorem expectation_coordinate {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1))
    (F : (∀ j, α j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂Measure.pi μ = ∫⁻ x, coordinateCredit μ i F x ∂μ i := by
  rw [pi_eq_map_split α μ i, lintegral_map hF (join α i).measurable]
  exact lintegral_prod (fun z => F (join α i z))
    (hF.comp (join α i).measurable).aemeasurable

/-- Updating the selected coordinate leaves its complementary conditional credit unchanged. -/
theorem coordinateCredit_update {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    (i : Fin (n + 1)) (ν : Measure (α i)) (F : (∀ j, α j) → ℝ≥0∞) :
    coordinateCredit (Function.update μ i ν) i F = coordinateCredit μ i F := by
  unfold coordinateCredit
  have htail : (fun j : Fin n => (Function.update μ i ν) (i.succAbove j)) =
      fun j => μ (i.succAbove j) := by
    funext j
    exact Function.update_of_ne (Fin.succAbove_ne i j) _ _
  rw [htail]

/-- The selected component may refine while every other component remains in the world. -/
theorem expectation_update {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1)) (ν : Measure (α i))
    [IsProbabilityMeasure ν] (F : (∀ j, α j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂Measure.pi (Function.update μ i ν) =
      ∫⁻ x, coordinateCredit μ i F x ∂ν := by
  have : ∀ j, IsProbabilityMeasure ((Function.update μ i ν) j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (inferInstance : IsProbabilityMeasure ν)
    · simpa only [Function.update_of_ne hj] using (inferInstance : IsProbabilityMeasure (μ j))
  rw [expectation_coordinate _ i F hF, coordinateCredit_update, Function.update_self]

end

end SampLib.FiniteProductPosterior
