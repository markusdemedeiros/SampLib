import SampLib.Syntax.PolynomialFactoryOpen
import SampLib.Samplers.BernoulliRace

/-! Source correspondence for polynomial callbacks in the rational factory. -/

open ProbLang

namespace SampLib.PolynomialFactory.RationalProgram

open FactoryFractions

variable {rT : Type}

private instance getAt_closed : ClosedExp (Occil.getAt : Exp rT) where
  lc := ListAccess.getAt_lc
  fv := ListAccess.getAt_fv

private instance choose_closed : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance polynomial_closed : ClosedExp (Occil.FactoryExtra.polynomial : Exp rT) where
  lc := by rw [Source.source_eq]; exact Source.source_lc
  fv := by simp [Occil.FactoryExtra.polynomial, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance race_closed : ClosedExp (Occil.bernoulliRace : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.bernoulliRace, Exp.fv, Occil.fairCoin]

def body : Exp rT :=
  .app (.app (.app Occil.bernoulliRace
    (.lam (.app (.app (.app Occil.FactoryExtra.polynomial (.bvar 4)) (.bvar 3)) (.lit .unit))))
    (.lam (.app (.app (.app Occil.FactoryExtra.polynomial (.bvar 4)) (.bvar 2)) (.lit .unit))))
    (.lit .unit)

theorem source_eq : (Occil.FactoryExtra.rationalFunction : Exp rT) =
    CurriedStep.lambdas 4 body := by
  simp [Occil.FactoryExtra.rationalFunction, CurriedStep.lambdas, body,
    Exp.close, Exp.closeRec, ClosedExp.closeRec]

theorem body_lcb : Exp.lcb 4 (body : Exp rT) = true := by
  have h : (Occil.FactoryExtra.rationalFunction : Exp rT).IsLocallyClosed := by is_lc
  rw [source_eq] at h
  simpa only [CurriedStep.lcb_lambdas, Nat.zero_add] using Exp.lc_imp_lcb h

section callbacks

variable [ProbLangℝ rT]

def polynomialCall (coin : Val rT) (xs : List Fraction) : Exp rT :=
  pl(&Occil.FactoryExtra.polynomial &coin.fst &(listVal Fraction.encode xs).fst #())

theorem call_lc (coin : Val rT) (xs : List Fraction) :
    (polynomialCall coin xs).IsLocallyClosed :=
  .app (.app (.app polynomial_closed.lc coin.lc) (listVal Fraction.encode xs).lc) Val.unit.lc

def polynomialValue (coin : Val rT) (xs : List Fraction) : Val rT :=
  have hc : (Exp.lam (polynomialCall coin xs)).IsLocallyClosed := by
    apply Exp.lcb_imp_lc
    change Exp.lcb 1 (polynomialCall coin xs) = true
    exact Exp.lcb_mono (Exp.lc_imp_lcb (call_lc coin xs)) (by omega)
  ⟨.lam (polynomialCall coin xs), .lam hc, hc⟩

theorem opened (coin : Val rT) (xs ys : List Fraction) :
    CurriedStep.opened
      [coin, listVal Fraction.encode xs, listVal Fraction.encode ys, Val.unit] body =
      pl(&Occil.bernoulliRace &(polynomialValue coin xs).fst
        &(polynomialValue coin ys).fst #()) := by
  simp [CurriedStep.opened, body, polynomialValue, polynomialCall,
    Exp.openRec, openRec_val_fst, ClosedExp.openRec]

end callbacks

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

theorem twp_open (E : CoPset) (coin : Val rT) (xs ys : List Fraction)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.bernoulliRace &(polynomialValue coin xs).fst
      &(polynomialValue coin ys).fst #()) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.rationalFunction &coin.fst
        &(listVal Fraction.encode xs).fst &(listVal Fraction.encode ys).fst #()) Φ := by
  rw [source_eq]
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (CurriedStep.application
        [coin, listVal Fraction.encode xs, listVal Fraction.encode ys, Val.unit]
        (CurriedStep.lambdas 4 body))) Φ)
  iapply (CurriedStep.twp_apply E []
    [coin, listVal Fraction.encode xs, listVal Fraction.encode ys, Val.unit] body body_lcb Φ)
  ieval (
    change _ ⊢ tglWp E (CurriedStep.opened
      [coin, listVal Fraction.encode xs, listVal Fraction.encode ys, Val.unit] body) Φ)
  rw [opened]
  iexact H

end specification

end SampLib.PolynomialFactory.RationalProgram
