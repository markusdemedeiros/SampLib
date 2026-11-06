import SampLib.Samplers.LogOnePlusRational
import SampLib.Samplers.ExpMinusScaled
import SampLib.Samplers.CoinProduct
import SampLib.Syntax.ClosedExp

/-! # Binary-exponential thinning without evaluating the unknown bias -/

open ProbLang
open scoped ENNReal

namespace SampLib.BinaryExponentialRational

noncomputable section

abbrev logTwo : unitInterval := LogOnePlusRational.bias 1 1 (by decide) (by decide) (by decide)

abbrev bias (p : unitInterval) (a b : ℕ) : unitInterval :=
  ExpMinusScaled.bias (p * logTwo) a b

/-- Multiplication by the exact log-two coin changes the base from `e` to two. -/
theorem bias_coe (p : unitInterval) (a b : ℕ) :
    (bias p a b : ℝ) = (2 : ℝ) ^ (-(a : ℝ) / b * p) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  simp only [bias, ExpMinusScaled.bias, Set.Icc.coe_mul, logTwo,
    LogOnePlusRational.bias_coe]
  norm_num only [Int.cast_one, div_one, one_add_one_eq_two]
  congr 1
  ring

def logarithmCallback {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam pl(if &coin.fst #() then &Occil.Constants.logOnePlusRational #1 #1 #() else #false),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private instance logarithm_closed : ClosedExp (Occil.Constants.logOnePlusRational : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Constants.logOnePlusRational, Occil.logOnePlusFactory,
      Occil.oneDivOnePlus, Occil.sampleGeometricBag, Occil.uniformBagStep,
      Occil.newUniformBag, Exp.fv, FairCoin.fairCoin_fv, RationalCoin.rationalCoin_fv]

private instance scaled_closed : ClosedExp (Occil.FactoryExtra.expMinusScaled : Exp rT) where
  lc := ExpMinusScaled.expMinusScaled_lc
  fv := ExpMinusScaled.expMinusScaled_fv

private theorem logTwo_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.logOnePlusRational #1 #1 #())
      (RealCoin.law logTwo) Val.bool :=
  LogOnePlusRational.logOnePlusRational_distSpec E 1 1 (by decide) (by decide) (by decide)

theorem logarithmCallback_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(logarithmCallback coin).fst #()) (RealCoin.law (p * logTwo))
      Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [← CoinProduct.expectation_preservation p logTwo F] at Hcredit
    iapply (hcoin.wp (CoinProduct.firstCredit logTwo F) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %r Hcredit
    cases r
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      iapply (logTwo_spec E).spec F (measurable_of_countable _) $$ Hcredit

/-- Poisson thinning receives the verified product callback. -/
theorem binaryExponentialRational_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ)
    (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.binaryExponentialRational &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p a b)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 4 twp_pure
    have hsample := (ExpMinusScaled.expMinusScaled_distSpec E (p * logTwo) a b hb
      (logarithmCallback coin) (logarithmCallback_distSpec E p coin hcoin)).spec F hF
    simp only [logarithmCallback] at hsample
    iapply hsample $$ Hcredit

end specification

end

end SampLib.BinaryExponentialRational
