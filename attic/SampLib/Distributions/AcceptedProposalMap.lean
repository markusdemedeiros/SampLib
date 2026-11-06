module

public import SampLib.Common.Laws.AcceptedProposal

@[expose] public section

/-! # Likelihood tilting commutes with an observable projection

A likelihood depending only on an observable may be normalized either on the
whole latent world or on its pushforward law. No independence is required.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.AcceptedProposal

noncomputable section

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  (μ : Measure Ω) (f : Ω → α) (hf : Measurable f)
  (φ : α → unitInterval) (hφ : Measurable φ)

include hf hφ in
/-- The total acceptance probability depends only on the observable's law. -/
theorem mass_map : mass μ (fun x => φ (f x)) = mass (μ.map f) φ := by
  rw [mass, mass, lintegral_map (measurable_weight φ hφ) hf]
  rfl

include hf hφ in
/-- Pushing forward a tilted latent world gives the corresponding tilted output law. -/
theorem law_map (hmass : mass μ (fun x => φ (f x)) ≠ 0) :
    (law μ (fun x => φ (f x)) hmass).map f =
      law (μ.map f) φ (by rwa [← mass_map μ f hf φ hφ]) := by
  rw [law, law, mass_map μ f hf φ hφ, Measure.map_smul _ hf.aemeasurable]
  congr 1
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hsource : Measurable (weight (fun x => φ (f x))) :=
    measurable_weight _ (hφ.comp hf)
  have hFsource : Measurable (fun x => F (f x)) := hF.comp hf
  rw [lintegral_map hF hf,
    lintegral_withDensity_eq_lintegral_mul _ hsource hFsource,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_weight φ hφ) hF,
    lintegral_map ((measurable_weight φ hφ).mul hF) hf]
  rfl

end

end SampLib.AcceptedProposal
