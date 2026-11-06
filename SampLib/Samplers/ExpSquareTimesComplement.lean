import SampLib.Samplers.AlternatingSeries
import SampLib.ExpSquareCoefficient
import Samplers.Bernoulli.Exponential

/-! # The factorial-pair factory for `exp(p²)(1-p)` -/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpSquareTimesComplement

noncomputable section

abbrev bias (p : unitInterval) : unitInterval :=
  AlternatingSeries.meanBias ExpSquareComplement.parameters p

theorem bias_coe (p : unitInterval) :
    (bias p : ℝ) = Real.exp ((p : ℝ) ^ 2) * (1 - p) := ExpSquareComplement.bias_coe p

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private def engine (coin : Val rT) : Exp rT :=
  pl(&Occil.FactoryExtra.alternatingSeries &coin.fst
    (fun n, (#1, (rec product n := if n <= #1 then #1 else n * product (n - #1))
      (n / #2))) #())

private theorem engine_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E (engine coin) (RealCoin.law (bias p)) Val.bool := by
  have h := AlternatingSeries.alternatingSeries_distSpec (rT := rT) (GF := GF) E
    ExpSquareComplement.parameters ExpSquareCoefficient.coefficient
    ExpSquareCoefficient.coefficient_eq p coin ExpSquareCoefficient.callback hcoin
    (ExpSquareCoefficient.twp_callback E)
  simpa [engine, ExpSquareCoefficient.callback, FactorialCallback.factorial, Exp.close,
    Exp.closeRec, Var.internal.injEq] using h

/-- Execute the lexical factorial, then apply the shared-uniform engine. -/
theorem expSquareTimesComplement_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.expSquareTimesComplement &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    ieval (change _ ⊢ tglWp E (engine coin) _)
    iapply (engine_spec E p coin hcoin).spec F hF $$ Hcredit

end specification

end

end SampLib.ExpSquareTimesComplement
