import SampLib.Distributions.ZetaThree
import SampLib.Samplers.FromPositiveSeries
import SampLib.PositiveSeriesClosed
import Samplers.Constants.Special

/-! # Occil's exact 3ζ(3)/4 coin -/

open ProbLang

namespace SampLib.ZetaThree

noncomputable section

@[pl_fold] private def getterCode {rT : Type} : Exp rT := pl%
  fun n,
    let k := n + #1;
    (#3, (#4 * k * k * k, (#3, #8 * k * k)))

private def getter {rT : Type} : Val rT :=
  ⟨getterCode, by unfold getterCode; exact .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_getter (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(getter : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromPositiveSeries.encodeCoefficient
        (parameters.coefficient n)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  simp [FromPositiveSeries.encodeCoefficient, parameters, coefficient,
    Nat.cast_add, Nat.cast_mul, Exp.ofVal]

/-- The actual getter supplies the convergent reciprocal-cube series and its tail. -/
theorem threeZetaThreeOverFour_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.threeZetaThreeOverFour #())
      (RealCoin.law (FromPositiveSeries.bias parameters)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    have h := (FromPositiveSeries.fromPositiveSeries_distSpec
      (rT := rT) (GF := GF) E parameters getter (twp_getter E)).spec F hF
    simp [getter, getterCode, Exp.close, Exp.closeRec] at h
    iapply h $$ Hcredit

end specification

end

end SampLib.ZetaThree
