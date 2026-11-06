module

public import SampLib.Latent.Laws.UniformProduct
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! # Joint dyadic posteriors for finitely many cached uniforms

Credits may depend on the entire latent vector. Revealing one coordinate
integrates the other coordinates without discarding their joint dependence.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

/-- Independent cached streams, before applying the caller's joint continuation credit. -/
def law {n : ℕ} (prefixes : Fin n → List Bool) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => DyadicPosterior.law (prefixes i))

instance {n : ℕ} (prefixes : Fin n → List Bool) : IsProbabilityMeasure (law prefixes) := by
  unfold law
  infer_instance

/-- Reassemble a chosen coordinate and the remaining coordinates in their original order. -/
def join {n : ℕ} (i : Fin (n + 1)) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm

/-- A coordinate permutation separates exactly one posterior from the remaining product. -/
theorem law_eq_map_split {n : ℕ} (prefixes : Fin (n + 1) → List Bool) (i : Fin (n + 1)) :
    law prefixes =
      ((DyadicPosterior.law (prefixes i)).prod
        (law (fun j => prefixes (i.succAbove j)))).map (join i) := by
  simpa only [law, join] using
    ((measurePreserving_piFinSuccAbove
      (fun j => DyadicPosterior.law (prefixes j)) i).symm _).map_eq.symm

/-- Every cached coordinate extends its own previous prefix. -/
def Refines {n : ℕ} (prefixes refined : Fin n → List Bool) : Prop :=
  ∀ i, prefixes i <+: refined i

/-- Reading one stream refines the product cache without changing other prefixes. -/
theorem refines_update {n : ℕ} (prefixes : Fin n → List Bool) (i : Fin n)
    (q : List Bool) (h : prefixes i <+: q) : Refines prefixes (Function.update prefixes i q) := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using h
  · simpa only [Function.update_of_ne hj] using List.prefix_refl (prefixes j)

/-- Simultaneous refinements preserve all null-set facts about the joint vector. -/
theorem law_refines {n : ℕ} {prefixes refined : Fin n → List Bool}
    (h : Refines prefixes refined) : law refined ≪ law prefixes := by
  induction n with
  | zero =>
    have heq : prefixes = refined := funext fun i => Fin.elim0 i
    rw [heq]
  | succ n ih =>
    rw [law_eq_map_split refined 0, law_eq_map_split prefixes 0]
    apply Measure.AbsolutelyContinuous.map _ (join 0).measurable
    exact (DyadicPosterior.law_refines (h 0)).prod
      (ih (fun j => h ((0 : Fin (n + 1)).succAbove j)))

/-- Credit for the chosen coordinate retains the exact joint continuation. -/
def coordinateCredit {n : ℕ} (prefixes : Fin (n + 1) → List Bool) (i : Fin (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ others, F (join i (x, others)) ∂law (fun j => prefixes (i.succAbove j))

theorem measurable_coordinateCredit {n : ℕ} (prefixes : Fin (n + 1) → List Bool)
    (i : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (coordinateCredit prefixes i F) :=
  (hF.comp (join i).measurable).lintegral_prod_right'

/-- Fubini in the chosen coordinate, for arbitrary measurable, possibly infinite credits. -/
theorem expectation_coordinate {n : ℕ} (prefixes : Fin (n + 1) → List Bool)
    (i : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂law prefixes =
      ∫⁻ x, coordinateCredit prefixes i F x ∂DyadicPosterior.law (prefixes i) := by
  rw [law_eq_map_split prefixes i, lintegral_map hF (join i).measurable]
  exact lintegral_prod (fun z => F (join i z)) (hF.comp (join i).measurable).aemeasurable

/-- Replacing one cached prefix leaves the integrated-out posteriors unchanged. -/
theorem coordinateCredit_update {n : ℕ} (prefixes : Fin (n + 1) → List Bool)
    (i : Fin (n + 1)) (q : List Bool) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) :
    coordinateCredit (Function.update prefixes i q) i F = coordinateCredit prefixes i F := by
  have hrest : (fun j => Function.update prefixes i q (i.succAbove j)) =
      (fun j => prefixes (i.succAbove j)) := by
    funext j
    exact Function.update_of_ne (Fin.succAbove_ne i j) _ _
  funext x
  simp only [coordinateCredit, hrest]

/-- The updated coordinate is integrated against its new posterior alone. -/
theorem expectation_update {n : ℕ} (prefixes : Fin (n + 1) → List Bool)
    (i : Fin (n + 1)) (q : List Bool) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F z ∂law (Function.update prefixes i q) =
      ∫⁻ x, coordinateCredit prefixes i F x ∂DyadicPosterior.law q := by
  rw [expectation_coordinate _ i F hF, coordinateCredit_update, Function.update_self]

/-- An almost-sure fact about a coordinate lifts to the entire product posterior. -/
theorem ae_coordinate {n : ℕ} (prefixes : Fin n → List Bool) (i : Fin n) {P : ℝ → Prop}
    (h : ∀ᵐ x ∂DyadicPosterior.law (prefixes i), P x) :
    ∀ᵐ z ∂law prefixes, P (z i) :=
  (measurePreserving_eval
    (fun j => DyadicPosterior.law (prefixes j)) i).quasiMeasurePreserving.ae h

/-- Finitely many coordinate facts hold together under the shared vector posterior. -/
theorem ae_coordinates {n : ℕ} (prefixes : Fin n → List Bool) {P : Fin n → ℝ → Prop}
    (h : ∀ i, ∀ᵐ x ∂DyadicPosterior.law (prefixes i), P i x) :
    ∀ᵐ z ∂law prefixes, ∀ i, P i (z i) :=
  ae_all_iff.mpr (fun i => ae_coordinate prefixes i (h i))

/-- Interval reads refer to the same selected coordinate of the shared latent vector. -/
theorem ae_encloses {n : ℕ} (prefixes : Fin n → List Bool) (i : Fin n)
    (I : LatentReal.RationalInterval)
    (h : ∀ᵐ x ∂DyadicPosterior.law (prefixes i), I.Contains x) :
    ∀ᵐ z ∂law prefixes, I.Contains (z i) :=
  ae_coordinate prefixes i h

end

end SampLib.UniformVector
