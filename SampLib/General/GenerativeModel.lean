import SampLib.Templates
import Samplers.General.DataModels
import Metrology.Iris.LocalBI
import SampLib.General.Laws.GenerativeModel

/-! # Sampling through a supplied deterministic generative model -/

open ProbLang
open scoped ENNReal

namespace SampLib.GenerativeModel

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
local bi (IProp GF)

theorem twp_generativeModel (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (latent decoder : Val rT)
    (encode : α → Val rT) (encode' : β → Val rT) (decode : α → β)
    (hdecode : Measurable decode)
    (hlatent : IsDistSpec (GF := GF) E pl(&latent.fst #()) μ encode)
    (hdecoder : ∀ x, ⊢ tglWp E pl(&decoder.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = encode' (decode x)⌝)))
    (F : β → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ y, F y ∂law μ decode) -∗
      tglWp E pl(&Occil.General.generativeModel &latent.fst &decoder.fst #())
        (fun v : Val rT => iprop(∃ y : β, ⌜v = encode' y⌝ ∗ ↯ (F y))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&latent.fst #())
  isimp only [← expectation μ decode hdecode F hF] at Hcredit
  iapply (hlatent.wp (fun x => F (decode x)) (hF.comp hdecode) _) $$ Hcredit
  iintro %x Hcredit
  twp_pure
  twp_bind pl(&decoder.fst &(encode x).fst)
  iapply tglWp_wand
  isplitl []
  · iapply hdecoder x
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists decode x
  iframe Hcredit
  ipureintro
  exact hv

/-- Typed pushforward specification for a supplied generative decoder. -/
theorem generativeModel_distSpec (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ]
    (latent decoder : Val rT) (encode : α → Val rT) (encode' : β → Val rT)
    (decode : α → β) (hdecode : Measurable decode)
    (hlatent : IsDistSpec (GF := GF) E pl(&latent.fst #()) μ encode)
    (hdecoder : ∀ x, ⊢ tglWp E pl(&decoder.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = encode' (decode x)⌝))) :
    letI := law_prob μ decode hdecode
    IsDistSpec (GF := GF) E pl(&Occil.General.generativeModel &latent.fst &decoder.fst #())
      (law μ decode) encode' := by
  let := law_prob μ decode hdecode
  exact ⟨fun F hF => wand_entails
    (twp_generativeModel E μ latent decoder encode encode' decode hdecode hlatent hdecoder F hF)⟩

end specification

end

end SampLib.GenerativeModel
