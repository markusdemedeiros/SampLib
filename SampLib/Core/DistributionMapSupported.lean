import SampLib.Core.SupportedSpec

/-! Transport a sampler's output encoding on an almost-sure support. -/

open Iris Iris.BI Iris.ProofMode ProbLang TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.IsDistSpec

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
variable {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}
local bi (IProp GF)

/-- Reinterpret outputs when their encodings agree on a measurable, almost-sure support. -/
theorem map_supported (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hs : ∀ᵐ x ∂μ, P x)
    (f : α → β) (hf : Measurable f) (encode' : β → Val rT)
    (hencode : ∀ x, P x → encode x = encode' (f x)) :
    IsDistSpec (GF := GF) E e (μ.map f) encode' where
  spec F hF := by
    rw [MeasureTheory.lintegral_map hF hf]
    iintro Hcredit
    iapply (h.wp_supported P hP hs (fun x => F (f x)) (hF.comp hf) _) $$ Hcredit
    iintro %x %hx Hcredit
    iexists f x
    iframe Hcredit
    ipureintro
    exact hencode x hx

end

end SampLib.IsDistSpec
