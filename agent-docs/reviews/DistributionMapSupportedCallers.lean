import SampLib.DistributionMapSupported

open ProbLang SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

-- The encoder agreement deliberately fails at the null output `false`.
example {E : CoPset} {e : Exp rT}
    (h : IsDistSpec (GF := GF) E e (MeasureTheory.Measure.dirac true) Val.bool) :
    IsDistSpec (GF := GF) E e (MeasureTheory.Measure.dirac ())
      (fun _ => Val.bool true) := by
  have hmap := h.map_supported (fun b => b = true) (measurableSet_singleton true)
    (by simp) (fun _ => ()) measurable_const (fun _ => Val.bool true)
    (fun b hb => by subst b; rfl)
  simpa only [MeasureTheory.Measure.map_dirac] using hmap

example {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}
    (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hs : ∀ᵐ x ∂μ, P x)
    (f : α → β) (hf : Measurable f) (encode' : β → Val rT)
    (he : ∀ x, P x → encode x = encode' (f x))
    (F : β → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ y, F y ∂μ.map f) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ y : β, ⌜v = encode' y⌝ ∗ ↯ (F y) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((h.map_supported P hP hs f hf encode' he).wp F hF _) $$ Hcredit
  iintro %y Hcredit
  iexists y
  iframe Hcredit HR
  itrivial

#print axioms IsDistSpec.map_supported
