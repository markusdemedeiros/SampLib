import SampLib.PSRN.Laws.PSRNDirichletLaw

open MeasureTheory SampLib.PSRNDirichletLaw
open scoped ENNReal

example {n : ℕ} (shape : Fin n → ℝ) (hs : ∀ i, 0 < shape i) :
    IsProbabilityMeasure (law shape hs) := inferInstance

example {n : ℕ} (hn : 0 < n) (shape : Fin n → ℝ) (hs : ∀ i, 0 < shape i) :
    ∀ᵐ x ∂law shape hs, (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 := ae_simplex shape hs hn

example (shape : Fin 1 → ℝ) (hs : ∀ i, 0 < shape i) :
    law shape hs = Measure.dirac (fun _ => 1) := law_singleton shape hs

example : simplex 1 = Measure.dirac (fun _ => 1) := law_singleton _ _

example {n : ℕ} (shape : Fin n → ℝ) (hs : ∀ i, 0 < shape i)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂law shape hs = ∫⁻ x, F (normalize x) ∂proposal shape hs :=
  expectation_preservation shape hs F hF

example : ∫⁻ y, (if y 0 = 1 then ∞ else 0) ∂simplex 1 = ∞ := by
  rw [show simplex 1 = Measure.dirac (fun _ => 1) from law_singleton _ _]
  simp

#print axioms ae_positive
#print axioms ae_simplex
#print axioms law_singleton
#print axioms expectation_preservation
#print axioms simplex_eq_exponentials
