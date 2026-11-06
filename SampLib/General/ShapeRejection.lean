import SampLib.Common.Syntax.Rejection
import Samplers.General.Core

/-! # Rejection into a measurable shape

The proposal may return structured values. The target is its law conditioned on
membership in the shape; positive acceptance mass supplies termination credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ShapeRejection

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- The wrapper inherits generic rejection's conditional law and termination argument. -/
theorem shapeRejection_distSpec (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal member : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (hmember : ∀ x, ⊢ tglWp E pl(&member.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.General.shapeRejection
      &proposal.fst &member.fst #()) (Rejection.law μ s hmass) encode where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    simp only [Rejection.rejection_openRec, Rejection.rejection_closeRec]
    iapply (Rejection.rejection_distSpec E μ s hs hmass encode proposal member
      hproposal hmember).spec F hF $$ Hcredit

end

end SampLib.ShapeRejection
