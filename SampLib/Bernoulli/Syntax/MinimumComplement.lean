import SampLib.Core.BetaStep
import SampLib.Bernoulli.Support.MinimumComplementWalk
import SampLib.Bernoulli.Support.MinimumComplementBinomial
import Samplers.Bernoulli.Series

/-! # Source correspondence for the minimum-complement factory -/

open ProbLang

namespace SampLib.MinimumComplement.Program

private instance fair_closed {rT : Type} : ClosedExp (Occil.fairCoin : Exp rT) where
  lc := FairCoin.fairCoin_lc
  fv := FairCoin.fairCoin_fv

private instance binomial_closed {rT : Type} : ClosedExp (Occil.binomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.binomial, Exp.fv]

private instance choose_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance power_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private instance rational_closed {rT : Type} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := RationalCoin.rationalCoin_lc
  fv := RationalCoin.rationalCoin_fv

private instance walk_closed {rT : Type} : ClosedExp (walk : Exp rT) where
  lc := walk_lc
  fv := walk_fv

def tailCode {rT : Type} : Exp rT :=
  bodyCode (fun depth => .bvar (depth + 3)) (fun depth => .bvar depth)

def sourceCore {rT : Type} : Exp rT :=
  let draw := Exp.app (.app (.bvar 0) pl(#0)) pl(#0)
  .app (.lam (.app (.lam tailCode) draw)) walk

def sourceBody {rT : Type} : Exp rT := .lam sourceCore

def sourceCode {rT : Type} : Exp rT := .lam sourceBody

def unitBody {rT : Type} (coin : Val rT) : Exp rT :=
  Exp.openRec 1 coin.fst sourceCore

def walkBody {rT : Type} (coin : Val rT) : Exp rT :=
  .app (.lam (Exp.openRec 2 (Val.unit : Val rT).fst (Exp.openRec 3 coin.fst tailCode)))
    (.app (.app (.bvar 0) pl(#0)) pl(#0))

def initialBody {rT : Type} (coin : Val rT) : Exp rT :=
  Exp.openRec 1 walk (Exp.openRec 2 (Val.unit : Val rT).fst (Exp.openRec 3 coin.fst tailCode))

theorem source_eq {rT : Type} :
    (Occil.FactoryExtra.minimumComplement : Exp rT) = sourceCode := by
  simp [Occil.FactoryExtra.minimumComplement, sourceCode, sourceBody, sourceCore, tailCode,
    bodyCode, walk,
    Exp.close, Exp.closeRec, Var.internal.injEq, ClosedExp.closeRec]

theorem opened_tail {rT : Type} (coin : Val rT) (m : ℕ) :
    Exp.open' (Exp.openRec 1 walk (Exp.openRec 2 (Val.unit : Val rT).fst
      (Exp.openRec 3 coin.fst tailCode))) (Val.int (m : ℤ)).fst =
      binomialBody coin m := by
  simp [tailCode, binomialBody, bodyCode, Exp.open', Exp.openRec, openRec_val_fst,
    ClosedExp.openRec]

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

theorem unit_lc {rT : Type} (coin : Val rT) : (Exp.lam (unitBody coin)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 0 (Exp.open' sourceBody coin.fst) = true
  apply Exp.lcb_openRec (Exp.lc_imp_lcb coin.lc)
  exact Exp.lc_imp_lcb source_lc

theorem opened_unit {rT : Type} (coin : Val rT) :
    Exp.open' (unitBody coin) (Val.unit : Val rT).fst = .app (.lam (walkBody coin)) walk := by
  simp [unitBody, sourceCore, walkBody, Exp.open', Exp.openRec, ClosedExp.openRec]

theorem walk_lc {rT : Type} (coin : Val rT) : (Exp.lam (walkBody coin)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.unit : Val rT).lc)
    (Exp.lc_imp_lcb (unit_lc coin))
  change Exp.lcb 0 (Exp.open' (unitBody coin) Val.unit.fst) = true at h
  rw [opened_unit] at h
  exact Exp.lcb_imp_lc (Bool.and_eq_true_iff.mp h).1

theorem opened_walk {rT : Type} (coin : Val rT) :
    Exp.open' (walkBody coin) (walk : Exp rT) =
      .app (.lam (initialBody coin)) pl(&walk #0 #0) := by
  simp [walkBody, initialBody, Exp.open', Exp.openRec]

theorem initial_lc {rT : Type} (coin : Val rT) :
    (Exp.lam (initialBody coin)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (MinimumComplement.walk_lc (rT := rT)))
    (Exp.lc_imp_lcb (walk_lc coin))
  change Exp.lcb 0 (Exp.open' (walkBody coin) walk) = true at h
  rw [opened_walk] at h
  exact Exp.lcb_imp_lc (Bool.and_eq_true_iff.mp h).1

section opening

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

private def walkValue : Val rT :=
  ⟨walk, .fix (MinimumComplement.walk_lc (rT := rT)), MinimumComplement.walk_lc⟩

theorem twp_open (E : CoPset) (coin : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (initialBody coin)) pl(&walk #0 #0)) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.minimumComplement &coin.fst #()) Φ := by
  rw [source_eq]
  iintro H
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill [.appL Val.unit] (.app (.lam sourceBody) coin.fst)) Φ)
  iapply (twp_beta E [.appL Val.unit] sourceBody coin source_lc Φ)
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam (unitBody coin)) Val.unit.fst)) Φ)
  iapply (twp_beta E [] (unitBody coin) Val.unit (unit_lc coin) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (unitBody coin) Val.unit.fst) Φ)
  rw [opened_unit]
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam (walkBody coin)) walkValue.fst)) Φ)
  iapply (twp_beta E [] (walkBody coin) walkValue (walk_lc coin) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (walkBody coin) walk) Φ)
  rw [opened_walk]
  iexact H

theorem twp_finish (E : CoPset) (coin : Val rT) (m : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (binomialBody coin m) Φ ⊢
      tglWp E (.app (.lam (initialBody coin)) (Val.int (m : ℤ)).fst) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT)
        (.app (.lam (initialBody coin)) (Val.int (m : ℤ)).fst)) Φ)
  iapply (twp_beta E [] (initialBody coin) (Val.int (m : ℤ)) (initial_lc coin) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (initialBody coin) (Val.int (m : ℤ)).fst) Φ)
  ieval (
    change _ ⊢ tglWp E
      (Exp.open' (Exp.openRec 1 walk (Exp.openRec 2 (Val.unit : Val rT).fst
        (Exp.openRec 3 coin.fst tailCode))) (Val.int (m : ℤ)).fst) Φ)
  rw [opened_tail]
  iexact H

end opening

end SampLib.MinimumComplement.Program
