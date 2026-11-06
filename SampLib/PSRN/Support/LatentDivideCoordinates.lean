import SampLib.PSRN.Support.LatentRepresentedDivision
import SampLib.Latent.LatentVectorSpec
import Samplers.PSRN.Geometry

/-! # Capturing a family of quotients with one shared denominator -/

open ProbLang

namespace SampLib.LatentReal.DivideCoordinates

noncomputable section

private instance divide_closed {rT : Type} : ClosedExp (Occil.PSRN.divide : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private def body {rT : Type} : Exp rT :=
  .case (.bvar 1) (.lam (.inl (.lit .unit)))
    (.lam (.inr (.pair (.app (.app Occil.PSRN.divide (.fst (.bvar 0))) (.bvar 1))
      (.app (.app (.bvar 3) (.snd (.bvar 0))) (.bvar 1)))))

private theorem source_eq {rT : Type} : (Occil.PSRN.divideCoordinates : Exp rT) =
    .fix (CurriedStep.lambdas 2 body) := by
  simp [Occil.PSRN.divideCoordinates, body, CurriedStep.lambdas, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq]

private theorem body_lcb {rT : Type} : Exp.lcb 3 (body : Exp rT) = true := by
  have h (k : ℕ) : Exp.lcb k (Occil.PSRN.divide : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (divide_closed (rT := rT)).lc) (Nat.zero_le k)
  simp [body, Exp.lcb, h]

private instance coordinates_closed {rT : Type} :
    ClosedExp (Occil.PSRN.divideCoordinates : Exp rT) where
  lc := by
    rw [source_eq]
    apply Exp.lcb_imp_lc
    change Exp.lcb 3 (body : Exp rT) = true
    exact body_lcb
  fv := by
    rw [source_eq]
    simp [CurriedStep.lambdas, body, Exp.fv, ClosedExp.fv]

private theorem opened {rT : Type} (xs denominator : Val rT) :
    CurriedStep.opened [xs, denominator]
      (Exp.openRec 2 (.fix (CurriedStep.lambdas 2 body)) body) =
      .case xs.fst (.lam (.inl (.lit .unit)))
        (.lam (.inr (.pair
          (.app (.app Occil.PSRN.divide (.fst (.bvar 0))) denominator.fst)
          (.app (.app Occil.PSRN.divideCoordinates (.snd (.bvar 0))) denominator.fst)))) := by
  rw [← source_eq]
  simp [CurriedStep.opened, body, Exp.openRec, ClosedExp.openRec, ProbLang.openRec_val_fst]

def values {rT : Type} {n : ℕ} (handles : Fin n → Val rT) (denominator : Val rT) :
    Fin n → Val rT := fun i => RepresentedDivision.value (handles i) denominator

private theorem encode_values {rT : Type} [ProbLangℝ rT] {n : ℕ}
    (handles : Fin (n + 1) → Val rT) (d : Val rT) :
    Exp.inr (.pair (RepresentedDivision.value (handles 0) d).fst
      (vectorVal (values (Fin.tail handles) d)).fst) =
        Exp.ofVal (vectorVal (values handles d)) := by
  simp only [Exp.ofVal, vectorVal, values, List.ofFn_succ, listVal]
  rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem twp_open (E : CoPset) (xs d : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (.case xs.fst (.lam (.inl (.lit .unit)))
      (.lam (.inr (.pair (.app (.app Occil.PSRN.divide (.fst (.bvar 0))) d.fst)
        (.app (.app Occil.PSRN.divideCoordinates (.snd (.bvar 0))) d.fst))))) Φ ⊢
      tglWp E pl(&Occil.PSRN.divideCoordinates &xs.fst &d.fst) Φ := by
  have h := CurriedStep.twp_fix_apply E [] xs [d] body (body_lcb (rT := rT)) Φ
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at h
  rw [opened] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem, Exp.ofVal]
      using h

/-- The list constructor captures each quotient without reading or copying the world. -/
theorem twp_constructor (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    {n : ℕ} (handles : Fin n → Val rT) (denominator : Val rT) (s : S) :
    withInvariant (RepresentedReciprocalView.Nonzero D) P s ⊢
      tglWp E pl(&Occil.PSRN.divideCoordinates &(vectorVal handles).fst &denominator.fst)
        (fun v => ViewOwns (vectorVal (values handles denominator))
          (withInvariant (RepresentedReciprocalView.Nonzero D) P) v s) := by
  induction n with
  | zero =>
    iintro Hstate
    iapply twp_open
    simp only [vectorVal, List.ofFn_zero, listVal]
    twp_pures
    twp_value
    imodintro
    isimp only [ViewOwns]
    iframe Hstate
  | succ n ih =>
    iintro Hstate
    iapply twp_open
    simp only [vectorVal, List.ofFn_succ, listVal]
    twp_pure
    twp_pure
    simp only [ClosedExp.openRec]
    twp_pure
    simp only [Exp.ofVal, id_eq]
    twp_bind pl(&Occil.PSRN.divideCoordinates &(vectorVal (Fin.tail handles)).fst
      &denominator.fst)
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply ih (Fin.tail handles) $$ Hstate
    iintro %tail Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%htail, Hstate⟩
    subst tail
    twp_pure
    twp_bind pl(&Occil.PSRN.divide &(handles 0).fst &denominator.fst)
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply RepresentedDivision.twp_constructor E D P (handles 0) denominator s $$ Hstate
    iintro %head Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hhead, Hstate⟩
    subst head
    simp only [Exp.ofVal]
    rw [encode_values]
    iapply (tglWp_value (v := vectorVal (values handles denominator)))
    isimp only [ViewOwns]
    iframe Hstate
    ipureintro
    simp [vectorVal, List.ofFn_succ, listVal]


end specification

end

end SampLib.LatentReal.DivideCoordinates
