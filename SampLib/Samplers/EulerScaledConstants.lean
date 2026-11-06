import SampLib.Samplers.EScaled
import SampLib.Distributions.EulerNumberBounds

/-! # The fixed rational scalings of Euler's number -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.EulerScaledConstants

noncomputable section

private theorem third_le_one : Real.exp 1 * (1 : ℕ) / (3 : ℕ) ≤ 1 := by
  simpa using (div_le_one (by norm_num : (0 : ℝ) < 3)).mpr EulerNumber.exp_one_lt_three.le

private theorem quarter_le_one : Real.exp 1 * (1 : ℕ) / (4 : ℕ) ≤ 1 := by
  have he := EulerNumber.exp_one_lt_three
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  linarith

abbrev third : unitInterval := EScaled.bias 1 3 third_le_one
abbrev quarter : unitInterval := EScaled.bias 1 4 quarter_le_one

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private instance scaled_closed : ClosedExp (Occil.Constants.eScaled : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.eScaled, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

/-- The named `e/3` coin is the verified factorial-bound sampler at scale `1/3`. -/
theorem eDivThree_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eDivThree #())
      (RealCoin.law third) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (EScaled.eScaled_distSpec E 1 3 (by decide) third_le_one).spec F hF $$ Hcredit

/-- The named `e/4` coin uses the same enclosure argument at scale `1/4`. -/
theorem eQuarter_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eQuarter #())
      (RealCoin.law quarter) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (EScaled.eScaled_distSpec E 1 4 (by decide) quarter_le_one).spec F hF $$ Hcredit

end specification

end

end SampLib.EulerScaledConstants
