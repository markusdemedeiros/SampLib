import SampLib.Samplers.ArctanOverPFactory
import SampLib.Samplers.RationalCoin
import Samplers.Constants.Pi

/-! # The arctangent ratio at a rational input

The input coin has bias `x/y`; the shared-uniform factory supplies atan(p)/p,
with the continuous value one when x is zero.
-/

open ProbLang

namespace SampLib.ArctanRationalOverRatio

noncomputable section

def bias (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y) : unitInterval :=
  ArctanOverPFactory.bias (RationalCoin.bias x y hx hy hxy)

theorem bias_coe (x y : ℤ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    (bias x y hx.le hy hxy : ℝ) = Real.arctan ((x : ℝ) / y) / ((x : ℝ) / y) := by
  apply ArctanFactory.ratio_coe_of_ne_zero
  exact ne_of_gt (div_pos (by exact_mod_cast hx) (by exact_mod_cast hy))

theorem bias_zero (y : ℤ) (hy : 0 < y) : bias 0 y (by omega) hy (by omega) = 1 := by
  apply Subtype.ext
  simp [bias, ArctanOverPFactory.bias, ArctanFactory.ratio, RationalCoin.bias]

private def coin {rT : Type} (x y : ℤ) : Val rT :=
  ⟨pl(fun v, &Occil.rationalCoin #int x #int y), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem coin_distSpec (E : CoPset) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y)
    (hxy : x ≤ y) :
    IsDistSpec (GF := GF) E pl(&(coin x y : Val rT).fst #())
      (RealCoin.law (RationalCoin.bias x y hx hy hxy)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    iapply ((RationalCoin.rationalCoin_distSpec E x y hx hy hxy).spec F hF) $$ Hcredit

theorem arctanRationalOverRatio_distSpec (E : CoPset) (x y : ℤ) (hx : 0 ≤ x)
    (hy : 0 < y) (hxy : x ≤ y) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.arctanRationalOverRatio #int x #int y #())
      (RealCoin.law (bias x y hx hy hxy)) Val.bool where
  spec F hF := by
    have hs := (ArctanOverPFactory.arctanOverPFactory_distSpec (rT := rT) (GF := GF) E
      (RationalCoin.bias x y hx hy hxy) (coin x y) (coin_distSpec E x y hx hy hxy)).spec F hF
    simp only [coin, Exp.close, Exp.closeRec, RationalCoin.rationalCoin_closeRec] at hs
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ArctanOverPFactory.arctanOverPFactory_openRec,
      ArctanOverPFactory.arctanOverPFactory_closeRec,
      RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    isimp only [bias] at Hcredit
    iapply hs $$ Hcredit

end specification

end

end SampLib.ArctanRationalOverRatio
