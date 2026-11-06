import SampLib.CurriedStep

open ProbLang Iris Iris.BI TotalEris ErisWpGS

namespace CurriedStepCallers

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Arbitrary callback values retain their free variables under the two beta steps. -/
example (E : CoPset) (K : Ectx rT) (fn arg : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill pl(&fn.fst &arg.fst)) Φ ⊢
      tglWp E (K.fill pl((fun f x, f x) &fn.fst &arg.fst)) Φ := by
  have h := SampLib.CurriedStep.twp_apply E K [fn, arg]
    (Exp.app (.bvar 1) (.bvar 0)) (by rfl) Φ
  simpa [SampLib.CurriedStep.opened, SampLib.CurriedStep.application,
    SampLib.CurriedStep.context, SampLib.CurriedStep.lambdas, Ectx.fill,
    EctxItem.fillItem, Exp.openRec, Exp.ofVal, flip, ProbLang.openRec_val_fst] using h

/-- The recursive binder and argument binder are opened in their distinct positions. -/
example (E : CoPset) (K : Ectx rT) (arg : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill arg.fst) Φ ⊢
      tglWp E (K.fill pl((rec again x := x) &arg.fst)) Φ := by
  have h := SampLib.CurriedStep.twp_fix_apply E K arg []
    (Exp.bvar 0) (by rfl) Φ
  simpa [SampLib.CurriedStep.opened, SampLib.CurriedStep.application,
    SampLib.CurriedStep.context, SampLib.CurriedStep.lambdas, Ectx.fill,
    EctxItem.fillItem, Exp.openRec, Exp.ofVal, flip] using h

end CurriedStepCallers

#print axioms SampLib.CurriedStep.twp_apply
#print axioms SampLib.CurriedStep.twp_fix_apply
