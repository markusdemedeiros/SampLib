module

public import SampLib.PSRN.Laws.PSRNDirichletLaw

@[expose] public section

/-! # Transporting a jointly constructed gamma vector through its common sum -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PSRNDirichletLaw

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- A jointly sampled gamma vector determines the normalized law, regardless of
its latent implementation or the handles used to expose its coordinates. -/
theorem law_eq_of_proposal (μ : Measure Ω) (values : Ω → Fin n → ℝ)
    (hvalues : Measurable values) (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i)
    (hproposal : μ.map values = proposal shape hshape) :
    μ.map (fun x => normalize (values x)) = law shape hshape := by
  rw [law, ← hproposal, Measure.map_map measurable_normalize hvalues]
  rfl

/-- The transport retains arbitrary joint continuation credits, including infinity. -/
theorem expectation_of_proposal (μ : Measure Ω) (values : Ω → Fin n → ℝ)
    (hvalues : Measurable values) (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i)
    (hproposal : μ.map values = proposal shape hshape)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (normalize (values x)) ∂μ = ∫⁻ y, F y ∂law shape hshape := by
  rw [← law_eq_of_proposal μ values hvalues shape hshape hproposal]
  exact (lintegral_map hF (measurable_normalize.comp hvalues)).symm

end

end SampLib.PSRNDirichletLaw
