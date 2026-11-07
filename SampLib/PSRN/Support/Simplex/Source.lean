import SampLib.PSRN.Syntax.PSRNSimplex

/-! # Checked source application and dimension guards for simplex construction -/

open ProbLang

namespace SampLib.PSRNSimplex.Program

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

theorem twp_open (E : CoPset) (components : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (openedBody components) Φ ⊢
      tglWp E pl(&Occil.PSRN.newSimplex #components #()) Φ := by
  have h := CurriedStep.twp_apply E [] [.int components, .unit] body (body_lcb (rT := rT)) Φ
  rw [opened_body] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← source_lambdas, ← source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem, Exp.ofVal]
    using h

end

end SampLib.PSRNSimplex.Program
