import SampLib.PSRN.Support.LatentRepresentedReciprocalView
import SampLib.PSRN.Support.LatentRepresentedMultiplication
import SampLib.PSRN.Support.LatentArithmeticMeasuredError
import SampLib.PSRN.Support.LatentWorldRelations
import SampLib.Core.CurriedStep

/-! # Division views sharing the same represented denominator -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.RepresentedDivision

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def model (L D : Model Ω S) (hworld : L.SameWorld D) (R : Representation D) : Model Ω S :=
  L.multiply (RepresentedReciprocal.model D R) (hworld.trans (RepresentedReciprocal.sameWorld D R))

def representation (L D : Model Ω S) (hworld : L.SameWorld D)
    (left : Representation L) (right : Representation D) :
    Representation (model L D hworld right) :=
  Representation.multiply L (RepresentedReciprocal.model D right)
    (hworld.trans (RepresentedReciprocal.sameWorld D right)) left
    (RepresentedReciprocal.representation D right)

theorem sameWorld (L D : Model Ω S) (hworld : L.SameWorld D) (R : Representation D) :
    L.SameWorld (model L D hworld R) :=
  (hworld.trans (RepresentedReciprocal.sameWorld D R)).multiply_left

theorem value_eq (L D : Model Ω S) (hworld : L.SameWorld D) (R : Representation D) (x : Ω) :
    (model L D hworld R).value x = L.value x / D.value x := by
  simp [model, Model.multiply, RepresentedReciprocal.model, div_eq_mul_inv]

theorem measurableError (L D : Model Ω S) (hworld : L.SameWorld D) (R : Representation D)
    (hleft : L.MeasurableError) : (model L D hworld R).MeasurableError :=
  hleft.multiply (RepresentedReciprocal.measurableError D R)
    (hworld.trans (RepresentedReciprocal.sameWorld D R))

def value {rT : Type} (a b : Val rT) : Val rT :=
  multiplyVal a (RepresentedReciprocal.Program.value b)

namespace Program

private instance multiply_closed {rT : Type} : ClosedExp (Occil.PSRN.multiply : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance reciprocal_closed {rT : Type} : ClosedExp (Occil.PSRN.reciprocal : Exp rT) where
  lc := by
    rw [RepresentedReciprocal.Program.source_eq]
    exact RepresentedReciprocal.Program.source_lc
  fv := by kernel_rfl

private def body {rT : Type} : Exp rT :=
  match (Occil.PSRN.divide : Exp rT) with
  | .lam (.lam result) => result
  | _ => .fail

private theorem source_eq {rT : Type} : (Occil.PSRN.divide : Exp rT) =
    CurriedStep.lambdas 2 body := by kernel_rfl

private theorem body_lcb {rT : Type} : Exp.lcb 2 (body : Exp rT) = true := by lcb_decide

private theorem opened_source {rT : Type} (a b : Val rT) :
    CurriedStep.opened [a, b] body =
      pl(&Occil.PSRN.multiply &a.fst (&Occil.PSRN.reciprocal &b.fst)) := by
  simp [CurriedStep.opened, body, Occil.PSRN.divide, Exp.openRec, Exp.close, Exp.closeRec,
    Var.internal.injEq, ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]

section specification

open Iris Iris.BI TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-- Apply the actual two-argument constructor without unfolding either operand. -/
theorem twp_open (E : CoPset) (a b : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.multiply &a.fst (&Occil.PSRN.reciprocal &b.fst)) Φ ⊢
      tglWp E pl(&Occil.PSRN.divide &a.fst &b.fst) Φ := by
  have h := CurriedStep.twp_apply E [] [a, b] body (body_lcb (rT := rT)) Φ
  rw [opened_source] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem, Exp.ofVal]
    using h

end specification

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Capturing a quotient preserves the physical world and its pure denominator invariant. -/
theorem twp_constructor (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (a b : Val rT) (s : S) :
    withInvariant (RepresentedReciprocalView.Nonzero D) P s ⊢
      tglWp E pl(&Occil.PSRN.divide &a.fst &b.fst)
        (fun v => ViewOwns (value a b)
          (withInvariant (RepresentedReciprocalView.Nonzero D) P) v s) := by
  iintro Hstate
  iapply Program.twp_open E a b _
  twp_bind pl(&Occil.PSRN.reciprocal &b.fst)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply RepresentedReciprocalView.twp_constructor E D P b s $$ Hstate
  iintro %v Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  subst v
  simp only [Exp.ofVal, value]
  iapply twp_multiply E a (RepresentedReciprocal.Program.value b)
    (withInvariant (RepresentedReciprocalView.Nonzero D) P) s $$ Hstate

/-- Quotient reads preserve aliases, the shared normalizer, and arbitrary joint credits. -/
theorem viewSpec (E : CoPset) (L D : Model Ω S) (hworld : L.SameWorld D)
    (left : Representation L) (right : Representation D) (P : S → IProp GF) (a b : Val rT)
    (ha : IsRepresentedViewSpec E L left P a) (hb : IsRepresentedViewSpec E D right P b) :
    IsRepresentedViewSpec E (model L D hworld right) (representation L D hworld left right)
      (withInvariant (RepresentedReciprocalView.Nonzero D) P) (value a b) := by
  have hleft := represented_view_withInvariant E L left P a ha
    (RepresentedReciprocalView.Nonzero D)
    (fun {_ _} hst => RepresentedReciprocalView.nonzero_refines D
      ((hworld.refines_iff _ _).mpr hst))
  exact represented_multiply_oracleSpec E L (RepresentedReciprocal.model D right)
    (hworld.trans (RepresentedReciprocal.sameWorld D right)) left
    (RepresentedReciprocal.representation D right)
    (withInvariant (RepresentedReciprocalView.Nonzero D) P) a
    (RepresentedReciprocal.Program.value b) hleft
    (RepresentedReciprocalView.viewSpec E D right P b hb)

end specification

end

end SampLib.LatentReal.RepresentedDivision
