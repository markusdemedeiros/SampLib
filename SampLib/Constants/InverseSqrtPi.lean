import SampLib.Constants.PiConstants
import SampLib.Bernoulli.FractionalPower
import SampLib.Core.Syntax.ClosedExp

/-! # The reciprocal square-root π coin

Apply the verified fractional-power construction to the reciprocal-π coin.
-/

open ProbLang

namespace SampLib.InverseSqrtPi

noncomputable section

def bias : unitInterval :=
  FractionalPower.bias PiConstants.inverseBias 1 2 (by norm_num) (by norm_num)

theorem bias_coe : (bias : ℝ) = 1 / Real.sqrt Real.pi := by
  simp only [bias, FractionalPower.bias, FractionalPower.powerBias,
    FractionalPower.exponent, Subtype.coe_mk, Nat.cast_one, Nat.cast_ofNat]
  rw [← Real.sqrt_eq_rpow, PiConstants.inverseBias_coe]
  simp only [one_div, Real.sqrt_inv]

private instance fractionalPower_closed {rT : Type} :
    ClosedExp (Occil.fractionalPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.fractionalPower, Exp.fv, RationalCoin.rationalCoin_fv]

private instance inversePi_closed {rT : Type} :
    ClosedExp (Occil.Constants.inversePi : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Constants.inversePi, Occil.Constants.reciprocalPiScaled,
      Occil.Constants.piBounds, Occil.Constants.arctanReciprocalBounds,
      Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv]

private def inverseCoin {rT : Type} : Val rT :=
  ⟨Occil.Constants.inversePi, by unfold Occil.Constants.inversePi; exact .lam (by is_lc),
    ClosedExp.lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

theorem inverseSqrtPi_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.inverseSqrtPi #())
      (RealCoin.law bias) Val.bool where
  spec F hF := by
    have hs := (FractionalPower.fractionalPower_distSpec (rT := rT) (GF := GF) E
      PiConstants.inverseBias 1 2 (by norm_num) (by norm_num)
      inverseCoin (PiConstants.inversePi_distSpec E)).spec F hF
    simp only [inverseCoin] at hs
    iintro Hcredit
    twp_pure
    isimp only [bias] at Hcredit
    iapply hs $$ Hcredit

end specification

end

end SampLib.InverseSqrtPi
