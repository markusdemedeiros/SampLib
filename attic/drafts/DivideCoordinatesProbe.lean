import SampLib.PSRN.Support.LatentRepresentedDivision
import SampLib.Latent.LatentVectorSpec
import Samplers.PSRN.Geometry

/-! # Capturing a family of quotients with one shared denominator -/

open ProbLang

set_option pp.notation false

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

set_option pp.maxDepth 7 in
private theorem opened {rT : Type} (xs denominator : Val rT) :
    CurriedStep.opened [xs, denominator]
      (Exp.openRec 2 (.fix (CurriedStep.lambdas 2 body)) body) =
      .case xs.fst (.lam (.inl (.lit .unit)))
        (.lam (.inr (.pair
          (.app (.app Occil.PSRN.divide (.fst (.bvar 0))) denominator.fst)
          (.app (.app Occil.PSRN.divideCoordinates (.snd (.bvar 0))) denominator.fst)))) := by
  rw [← source_eq]
  simp [CurriedStep.opened, body, Exp.openRec, ClosedExp.openRec, ProbLang.openRec_val_fst]

end
end SampLib.LatentReal.DivideCoordinates
