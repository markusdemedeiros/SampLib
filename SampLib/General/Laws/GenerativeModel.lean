import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Generative model law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.GenerativeModel

noncomputable section

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

/-- The model pushes the latent distribution forward through its decoder. -/
def law (μ : Measure α) (decode : α → β) : Measure β := μ.map decode

theorem law_prob (μ : Measure α) [IsProbabilityMeasure μ] (decode : α → β)
    (hdecode : Measurable decode) :
    IsProbabilityMeasure (law μ decode) where
  measure_univ := by
    rw [law, Measure.map_apply hdecode MeasurableSet.univ]
    simp

/-- Decoder composition is change of variables for the latent expectation. -/
theorem expectation (μ : Measure α) (decode : α → β) (hdecode : Measurable decode)
    (F : β → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (decode x) ∂μ = ∫⁻ y, F y ∂law μ decode := by
  rw [law, lintegral_map hF hdecode]

end

end SampLib.GenerativeModel
