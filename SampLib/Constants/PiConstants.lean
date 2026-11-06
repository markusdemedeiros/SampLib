import SampLib.Constants.PiAffine
import SampLib.Constants.ReciprocalPiScaled

/-! # Named probabilities in π

These are the named specializations of the verified affine and reciprocal Machin
constructions. Their expectation argument and termination proof are inherited unchanged.
-/

open ProbLang

namespace SampLib.PiConstants

noncomputable section

private theorem pi_lower : 3 < Real.pi :=
  (PiBounds.interval_positive 0).trans_le (PiBounds.interval 0).left_le

private theorem pi_upper : Real.pi < 4 := by
  refine (PiBounds.interval 0).le_right.trans_lt ?_
  norm_num [RealEnclosure.Interval.right, PiBounds.interval, PiBounds.piRaw,
    PiBounds.arctanRaw, PiBounds.numerator, PiBounds.denominator,
    PiBounds.termDenominator, PiBounds.sign]

def quarterBias : unitInterval :=
  PiProbability.affineBias 0 4 (by norm_num) (by simpa using Real.pi_pos.le)
    (by simpa using pi_upper.le)

def twelfthBias : unitInterval :=
  PiProbability.affineBias 0 12 (by norm_num) (by simpa using Real.pi_pos.le)
    (by simp only [Int.cast_zero, sub_zero, Nat.cast_ofNat]; linarith [pi_upper])

def quarterMinusHalfBias : unitInterval :=
  PiProbability.affineBias 2 4 (by norm_num) (by norm_num; linarith [pi_lower])
    (by norm_num; linarith [pi_upper])

def minusThreeOverFourBias : unitInterval :=
  PiProbability.affineBias 3 4 (by norm_num) (by norm_num; linarith [pi_lower])
    (by norm_num; linarith [pi_upper])

def minusThreeBias : unitInterval :=
  PiProbability.affineBias 3 1 (by norm_num) (by norm_num; linarith [pi_lower])
    (by norm_num; linarith [pi_upper])

def inverseBias : unitInterval :=
  ReciprocalPiProbability.bias 1 1 (by norm_num) (by norm_num; linarith [pi_lower])

def fourOverThreeBias : unitInterval :=
  ReciprocalPiProbability.bias 4 3 (by norm_num) (by norm_num; linarith [pi_lower])

theorem quarterBias_coe : (quarterBias : ℝ) = Real.pi / 4 := by
  simp [quarterBias, PiProbability.affineBias]

theorem twelfthBias_coe : (twelfthBias : ℝ) = Real.pi / 12 := by
  simp [twelfthBias, PiProbability.affineBias]

theorem quarterMinusHalfBias_coe :
    (quarterMinusHalfBias : ℝ) = Real.pi / 4 - 1 / 2 := by
  simp only [quarterMinusHalfBias, PiProbability.affineBias, Int.cast_ofNat,
    Nat.cast_ofNat, Subtype.coe_mk]
  ring

theorem minusThreeOverFourBias_coe : (minusThreeOverFourBias : ℝ) = (Real.pi - 3) / 4 := rfl

theorem minusThreeBias_coe : (minusThreeBias : ℝ) = Real.pi - 3 := by
  simp [minusThreeBias, PiProbability.affineBias]

theorem inverseBias_coe : (inverseBias : ℝ) = 1 / Real.pi := by
  simp [inverseBias, ReciprocalPiProbability.bias]

theorem fourOverThreeBias_coe : (fourOverThreeBias : ℝ) = 4 / (3 * Real.pi) := rfl

private instance piBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.piBounds : Exp rT) where
  lc := PiBounds.piBounds_lc
  fv := PiBounds.piBounds_fv

private instance fromBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.fromBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
    UniformBag.uniformBagLess_fv]

private instance piAffine_closed {rT : Type} :
    ClosedExp (Occil.Constants.piAffine : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.piAffine, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance reciprocalPiScaled_closed {rT : Type} :
    ClosedExp (Occil.Constants.reciprocalPiScaled : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.reciprocalPiScaled, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

theorem piQuarter_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.piQuarter #())
      (RealCoin.law quarterBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [quarterBias] at Hcredit
    iapply ((PiAffine.piAffine_distSpec E 0 4 _ _ _).spec F hF) $$ Hcredit

theorem piTwelfth_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.piTwelfth #())
      (RealCoin.law twelfthBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [twelfthBias] at Hcredit
    iapply ((PiAffine.piAffine_distSpec E 0 12 _ _ _).spec F hF) $$ Hcredit

theorem piQuarterMinusHalf_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.piQuarterMinusHalf #())
      (RealCoin.law quarterMinusHalfBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [quarterMinusHalfBias] at Hcredit
    iapply ((PiAffine.piAffine_distSpec E 2 4 _ _ _).spec F hF) $$ Hcredit

theorem piMinusThreeOverFour_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.piMinusThreeOverFour #())
      (RealCoin.law minusThreeOverFourBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [minusThreeOverFourBias] at Hcredit
    iapply ((PiAffine.piAffine_distSpec E 3 4 _ _ _).spec F hF) $$ Hcredit

theorem piMinusThree_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.piMinusThree #())
      (RealCoin.law minusThreeBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [minusThreeBias] at Hcredit
    iapply ((PiAffine.piAffine_distSpec E 3 1 _ _ _).spec F hF) $$ Hcredit

theorem inversePi_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.inversePi #())
      (RealCoin.law inverseBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [inverseBias] at Hcredit
    iapply ((ReciprocalPiScaled.reciprocalPiScaled_distSpec E 1 1 _ _).spec F hF) $$ Hcredit

theorem fourOverThreePi_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.fourOverThreePi #())
      (RealCoin.law fourOverThreeBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [fourOverThreeBias] at Hcredit
    iapply ((ReciprocalPiScaled.reciprocalPiScaled_distSpec E 4 3 _ _).spec F hF) $$ Hcredit

end specification

end

end SampLib.PiConstants
