import SampLib.Bernoulli.ArctanFactory
import SampLib.Constants.PiConstants
import Samplers.Bernoulli.Trigonometric

/-! # Arctangent divided by pi

An independent inverse-pi selector scales the verified arctangent coin.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ArctanOverPi

noncomputable section

def bias (p : unitInterval) : unitInterval := PiConstants.inverseBias * ArctanFactory.bias p

@[simp] theorem bias_coe (p : unitInterval) : (bias p : ℝ) = Real.arctan p / Real.pi := by
  simp only [bias, Set.Icc.coe_mul, PiConstants.inverseBias_coe, ArctanFactory.bias_coe]
  ring

private theorem inverse_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.inversePi = Occil.Constants.inversePi :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem inverse_fv {rT : Type} : (Occil.Constants.inversePi : Exp rT).fv = ∅ := by
  simp [Occil.Constants.inversePi, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private theorem inverse_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.inversePi : Exp rT) = Occil.Constants.inversePi :=
  Exp.closeRec_fresh x _ k (by simp [inverse_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Exact arctangent scaling, for every input bias in the closed unit interval. -/
theorem arctanOverPi_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.arctanOverPi &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [inverse_open, inverse_close]
    twp_bind pl(&Occil.Constants.inversePi #())
    isimp only [bias, ← CoinProduct.expectation_preservation PiConstants.inverseBias
      (ArctanFactory.bias p) F] at Hcredit
    iapply ((PiConstants.inversePi_distSpec E).wp
      (CoinProduct.firstCredit (ArctanFactory.bias p) F) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      simp only [ArctanFactory.arctanFactory_openRec, ArctanFactory.arctanFactory_closeRec]
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      iapply (ArctanFactory.arctanFactory_distSpec E p coin hcoin).spec F hF $$ Hcredit

end specification

end

end SampLib.ArctanOverPi
