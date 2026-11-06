import SampLib.Templates

/-! Transport a sampler specification along a measurable output map. -/

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

/-- Reinterpret the mathematical result when the two output encodings agree. -/
theorem map (h : IsDistSpec (GF := GF) E e μ encode) (f : α → β) (hf : Measurable f)
    (encode' : β → Val rT) (hencode : ∀ x, encode x = encode' (f x)) :
    IsDistSpec (GF := GF) E e (μ.map f) encode' where
  spec F hF := by
    rw [MeasureTheory.lintegral_map hF hf]
    iintro Hcredit
    iapply (h.wp (fun x => F (f x)) (hF.comp hf) _) $$ Hcredit
    iintro %x Hcredit
    iexists f x
    iframe Hcredit
    ipureintro
    exact hencode x

end

end SampLib.IsDistSpec
