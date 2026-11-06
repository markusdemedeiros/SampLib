import SampLib.LatentRepresentedUnary
import SampLib.CurriedStep
import SampLib.Syntax.ClosedExp

/-! # Subtracting a shared source from a rational point -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

/-- The literal subtraction result captures the same source through negation. -/
def subtractFromPointVal {rT : Type} (source : Val rT) (a b : ℤ) : Val rT :=
  translateVal (negateVal source) a b

private theorem add_point {rT : Type} (source : Val rT) (a b : ℤ) :
    addVal (LatentRational.value a b) source = translateVal source a b := by
  apply Val.ext
  rfl

namespace PointSubtract

private instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance negate_closed {rT : Type} : ClosedExp (Occil.PSRN.negate : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def body {rT : Type} : Exp rT :=
  match (Occil.PSRN.subtract : Exp rT) with
  | .lam (.lam result) => result
  | _ => .fail

private theorem source_eq {rT : Type} : (Occil.PSRN.subtract : Exp rT) =
    CurriedStep.lambdas 2 body := by kernel_rfl

private theorem body_lcb {rT : Type} : Exp.lcb 2 (body : Exp rT) = true := by lcb_decide

private theorem opened {rT : Type} (left right : Val rT) :
    CurriedStep.opened [left, right] body =
      pl(&Occil.PSRN.add &left.fst (&Occil.PSRN.negate &right.fst)) := by
  simp [CurriedStep.opened, body, Occil.PSRN.subtract, Exp.openRec, Exp.close, Exp.closeRec,
    ClosedExp.openRec, ClosedExp.closeRec, Var.internal.injEq, ProbLang.openRec_val_fst]

end PointSubtract

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem twp_point (E : CoPset) (P : S → IProp GF) (s : S)
    (a b : ℤ) (hb : 0 < b) :
    P s ⊢ tglWp E pl(&Occil.PSRN.rational #a #b)
      (fun v => ViewOwns (LatentRational.value a b) P v s) := by
  iintro Hstate
  twp_pures
  rw [decide_eq_false (not_le.mpr hb)]
  twp_pures
  twp_value
  imodintro
  isimp only [ViewOwns]
  iframe Hstate
  ipureintro
  rfl

private theorem twp_subtract_open (E : CoPset) (left right : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.add &left.fst (&Occil.PSRN.negate &right.fst)) Φ ⊢
      tglWp E pl(&Occil.PSRN.subtract &left.fst &right.fst) Φ := by
  have h := CurriedStep.twp_apply E [] [left, right] PointSubtract.body
    (PointSubtract.body_lcb (rT := rT)) Φ
  rw [PointSubtract.opened] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← PointSubtract.source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem, Exp.ofVal]
    using h

/-- The original point-minus-source constructor performs no observations. -/
theorem twp_subtractFromPoint (E : CoPset) (source : Val rT) (P : S → IProp GF) (s : S)
    (a b : ℤ) (hb : 0 < b) :
    P s ⊢ tglWp E pl(&Occil.PSRN.subtract (&Occil.PSRN.rational #a #b) &source.fst)
      (fun v => ViewOwns (subtractFromPointVal source a b) P v s) := by
  iintro Hstate
  twp_bind pl(&Occil.PSRN.rational #a #b)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_point E P s a b hb $$ Hstate
  iintro %point Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hp, Hstate⟩
  subst point
  simp only [Exp.ofVal]
  iapply twp_subtract_open E (LatentRational.value a b) source _
  twp_bind pl(&Occil.PSRN.negate &source.fst)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_negate_view E source P s $$ Hstate
  iintro %negative Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hn, Hstate⟩
  subst negative
  simp only [Exp.ofVal, subtractFromPointVal]
  have h := twp_add E (LatentRational.value a b) (negateVal source) P s
  rw [add_point] at h
  iapply h $$ Hstate

/-- Both arithmetic views share the original physical resource and exact interval schedule. -/
theorem represented_subtractFromPoint_viewSpec (E : CoPset) (D : Model Ω S)
    (R : Representation D) (P : S → IProp GF) (source : Val rT)
    (hsource : IsRepresentedViewSpec E D R P source) (a b : ℤ) (hb : 0 < b) :
    IsRepresentedViewSpec E (D.negate.translate ((a : ℝ) / b))
      (Representation.translate D.negate (Representation.negate D R) a b hb)
      P (subtractFromPointVal source a b) :=
  represented_translate_viewSpec E D.negate (Representation.negate D R) P (negateVal source)
    (represented_negate_viewSpec E D R P source hsource) a b hb

end specification

end

end SampLib.LatentReal
