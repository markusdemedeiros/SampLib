module

public import SampLib.Latent.Laws.UniformVector

@[expose] public section

open MeasureTheory SampLib
open scoped ENNReal

example (prefixes : Fin 0 → List Bool) : IsProbabilityMeasure (UniformVector.law prefixes) :=
  inferInstance

example {n : ℕ} (prefixes : Fin (n + 1) → List Bool) (i : Fin (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂UniformVector.law prefixes =
      ∫⁻ x, UniformVector.coordinateCredit prefixes i F x
        ∂DyadicPosterior.law (prefixes i) :=
  UniformVector.expectation_coordinate prefixes i F hF

example {n : ℕ} (prefixes : Fin (n + 1) → List Bool) (i : Fin (n + 1))
    (q : List Bool) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂UniformVector.law (Function.update prefixes i q) =
      ∫⁻ x, UniformVector.coordinateCredit prefixes i F x ∂DyadicPosterior.law q :=
  UniformVector.expectation_update prefixes i q F hF

example (prefixes : Fin 1 → List Bool) :
    ∫⁻ _z, (⊤ : ℝ≥0∞) ∂UniformVector.law prefixes =
      ∫⁻ x, UniformVector.coordinateCredit prefixes 0 (fun _ => ⊤) x
        ∂DyadicPosterior.law (prefixes 0) :=
  UniformVector.expectation_coordinate prefixes 0 (fun _ => ⊤) measurable_const

example (prefixes : Fin 3 → List Bool) (i : Fin 3) (q : List Bool)
    (h : prefixes i <+: q) :
    UniformVector.law (Function.update prefixes i q) ≪ UniformVector.law prefixes :=
  UniformVector.law_refines (UniformVector.refines_update prefixes i q h)

example {n : ℕ} (prefixes : Fin n → List Bool) (P : Fin n → ℝ → Prop)
    (h : ∀ i, ∀ᵐ x ∂DyadicPosterior.law (prefixes i), P i x) :
    ∀ᵐ z ∂UniformVector.law prefixes, ∀ i, P i (z i) :=
  UniformVector.ae_coordinates prefixes h

#print axioms SampLib.UniformVector.law_refines
#print axioms SampLib.UniformVector.law_eq_map_split
#print axioms SampLib.UniformVector.measurable_coordinateCredit
#print axioms SampLib.UniformVector.expectation_coordinate
#print axioms SampLib.UniformVector.expectation_update
#print axioms SampLib.UniformVector.ae_coordinates
