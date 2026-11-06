import SampLib.Core.ListEncoding
import SampLib.Templates
import Samplers.General.Core
import SampLib.General.Laws.ListMapSampling

/-! # Independent sampling along a list of callback arguments -/

open ProbLang
open scoped ENNReal

namespace SampLib.ListMapSampling

noncomputable section

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] {β : Type _}
    (encode : β → Val rT) (y : β) (ys : List β) :
    pl(inr(({Exp.ofVal (encode y)}, {Exp.ofVal (listVal encode ys)}))) =
      Exp.ofVal (listVal encode (y :: ys)) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α β : Type _} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
local bi (IProp GF)

/-- Repeated calls to the callback preserve the independent kernel-list law. -/
theorem twp_map (E : CoPset) (μ : α → MeasureTheory.Measure β)
    [∀ x, MeasureTheory.IsProbabilityMeasure (μ x)] (input : α → Val rT)
    (output : β → Val rT) (callback : Val rT)
    (hcallback : ∀ x, IsDistSpec (GF := GF) E pl(&callback.fst &(input x).fst) (μ x) output)
    (xs : List α) (F : List β → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law μ xs) -∗
      tglWp E pl(&Occil.General.map &callback.fst &(listVal input xs).fst)
        (fun v : Val rT => iprop(∃ ys : List β, ⌜v = listVal output ys⌝ ∗ ↯ (F ys))) := by
  induction xs generalizing F with
  | nil =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | cons x xs IH =>
    iintro Hcredit
    simp only [listVal]
    iterate 6 twp_pure
    twp_bind pl(&Occil.General.map &callback.fst &(listVal input xs).fst)
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation μ x xs F] at Hcredit
      iapply IH $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    twp_pure
    twp_bind pl(&callback.fst &(input x).fst)
    iapply ((hcallback x).wp (fun y => F (y :: ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %y Hcredit
    rw [encode_cons]
    iapply (tglWp_value (v := listVal output (y :: ys)))
    iexists y :: ys
    iframe Hcredit
    itrivial

/-- Supporting specification for a stochastic list map. -/
theorem map_distSpec (E : CoPset) (μ : α → MeasureTheory.Measure β)
    [∀ x, MeasureTheory.IsProbabilityMeasure (μ x)] (input : α → Val rT)
    (output : β → Val rT) (callback : Val rT)
    (hcallback : ∀ x, IsDistSpec (GF := GF) E pl(&callback.fst &(input x).fst) (μ x) output)
    (xs : List α) :
    IsDistSpec (GF := GF) E pl(&Occil.General.map &callback.fst &(listVal input xs).fst)
      (law μ xs) (listVal output) where
  spec F _ := wand_entails (twp_map E μ input output callback hcallback xs F)

end specification

end

end SampLib.ListMapSampling
