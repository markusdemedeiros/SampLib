import SampLib.Uniform.RationalCoin
import SampLib.General.Laws.CappedRationalCoin

/-! # The capped rational acceptance test used by Metropolis kernels -/

open ProbLang
open scoped ENNReal

namespace SampLib.CappedRationalCoin

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] [ProbLangDist.IsUniformInt rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The saturation branch avoids calling the bounded coin outside its input domain. -/
theorem distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E
      pl(if #int b <= #int a then #true else &Occil.rationalCoin #int a #int b)
      (RealCoin.law (bias a b ha hb)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    by_cases h : b ≤ a
    · rw [decide_eq_true h]
      twp_pure
      twp_value
      imodintro
      iexists true
      isimp only [full_expectation a b ha hb h] at Hcredit
      iframe Hcredit
      itrivial
    · rw [decide_eq_false h]
      twp_pure
      have hab : a ≤ b := le_of_lt (lt_of_not_ge h)
      isimp only [bias_fraction a b ha hb hab] at Hcredit
      iapply ((RationalCoin.rationalCoin_distSpec E a b ha hb hab).wp F hF _) $$ Hcredit
      iintro %z Hcredit
      iexists z
      iframe Hcredit
      itrivial

end specification

end

end SampLib.CappedRationalCoin
