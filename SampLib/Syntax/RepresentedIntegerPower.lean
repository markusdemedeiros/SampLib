import SampLib.CurriedStep
import SampLib.Syntax.ClosedExp
import Samplers.PSRN.Arithmetic

/-! # Opening the actual repeated-squaring constructor without capturing handles -/

open ProbLang

namespace SampLib.LatentReal.IntegerPower.Program

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance multiply_closed {rT : Type} : ClosedExp (Occil.PSRN.multiply : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance source_closed {rT : Type} : ClosedExp (Occil.PSRN.integerPowerReal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.LatentReal.IntegerPower.Program

def code {rT : Type} : Exp rT :=
  match (Occil.PSRN.integerPowerReal : Exp rT) with
  | .fix (.lam (.lam body)) => body
  | _ => .fail

theorem code_lcb {rT : Type} : Exp.lcb 3 (code : Exp rT) = true := by lcb_decide

theorem source_eq {rT : Type} : (Occil.PSRN.integerPowerReal : Exp rT) =
    .fix (CurriedStep.lambdas 2 code) := by kernel_rfl

/-- The two let binders are built before inserting the arbitrary source handle. -/
def body {rT : Type} (source : Val rT) (n : ℤ) : Exp rT :=
  let afterSquare : Exp rT := pl(if #int n % #2 = #0 then {Exp.bvar 0} else
    &Occil.PSRN.multiply &source.fst {Exp.bvar 0})
  let afterHalf := Exp.app (.lam afterSquare)
    pl(&Occil.PSRN.multiply {Exp.bvar 0} {Exp.bvar 0})
  let recurse := Exp.app (.lam afterHalf)
    pl(&Occil.PSRN.integerPowerReal &source.fst (#int n / #2))
  pl% if #int n < #0 then fail else if #int n = #0 then &Occil.PSRN.rational #1 #1 else
    if #int n = #1 then &source.fst else &recurse

theorem opened_source {rT : Type} (source : Val rT) (n : ℤ) :
    CurriedStep.opened [source, Val.int n]
      (Exp.openRec 2 Occil.PSRN.integerPowerReal code) = body source n := by
  simp [CurriedStep.opened, code, body, Occil.PSRN.integerPowerReal,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]

section specification

open Iris Iris.BI TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- One checked recursive unfolding and two argument steps expose the source guards. -/
theorem twp_open (E : CoPset) (source : Val rT) (n : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (body source n) Φ ⊢
      tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #int n) Φ := by
  have h := CurriedStep.twp_fix_apply E [] source [Val.int n] code code_lcb Φ
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at h
  rw [← source_eq, opened_source] at h
  simpa only [CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, EctxItem.fillItem, Exp.ofVal, flip] using h

end specification

end SampLib.LatentReal.IntegerPower.Program
