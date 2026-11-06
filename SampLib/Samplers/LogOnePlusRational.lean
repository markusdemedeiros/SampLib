import SampLib.Samplers.LogOnePlusFactory
import SampLib.Samplers.RationalCoin
import Samplers.Constants.Special

/-! # The logarithmic coin at a rational input

The wrapper supplies a rational coin to the verified lazy-uniform logarithm factory.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LogOnePlusRational

noncomputable section

abbrev bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :=
  LogOnePlusFactory.bias (RationalCoin.bias a b ha hb hab)

@[simp] theorem bias_coe (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    (bias a b ha hb hab : ℝ) = Real.log (1 + (a : ℝ) / b) := rfl

private def coin {rT : Type} (a b : ℤ) : Val rT :=
  ⟨.lam (.app (.app Occil.rationalCoin (.lit (.int a))) (.lit (.int b))),
    .lam (by is_lc), by is_lc⟩

private theorem logarithm_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.logOnePlusFactory = Occil.logOnePlusFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem logarithm_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.logOnePlusFactory : Exp rT) = Occil.logOnePlusFactory :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.logOnePlusFactory, Occil.oneDivOnePlus, Occil.sampleGeometricBag,
      Occil.uniformBagStep, Occil.newUniformBag, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem coin_spec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&(coin a b : Val rT).fst #())
      (RealCoin.law (RationalCoin.bias a b ha hb hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    iapply (RationalCoin.rationalCoin_distSpec E a b ha hb hab).spec F hF $$ Hcredit

/-- The actual wrapper has bias `log(1+a/b)`, including both input endpoints. -/
theorem logOnePlusRational_distSpec (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.logOnePlusRational #int a #int b #())
      (RealCoin.law (bias a b ha hb hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    isimp only [logarithm_open, logarithm_close, RationalCoin.rationalCoin_openRec,
      RationalCoin.rationalCoin_closeRec]
    have hsample := (LogOnePlusFactory.logOnePlusFactory_distSpec (rT := rT) (GF := GF) E
      (RationalCoin.bias a b ha hb hab) (coin a b) (coin_spec E a b ha hb hab)).spec F hF
    simp only [coin] at hsample
    iapply hsample $$ Hcredit

end specification

end

end SampLib.LogOnePlusRational
