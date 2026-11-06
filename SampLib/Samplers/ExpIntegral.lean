import SampLib.Samplers.AlternatingSeries
import SampLib.Samplers.ExpIntegralPositive
import SampLib.ExpIntegralCoefficient

/-! # The factorial-integral factory on its complete nonnegative integer-shift domain -/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpIntegral

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private def zeroEngine (coin : Val rT) : Exp rT :=
  pl(&Occil.FactoryExtra.alternatingSeries &coin.fst
    (fun n,
      let factorial := (rec product k := if k <= #1 then #1 else k * product (k - #1));
      (#1, factorial (n + #1))) #())

private theorem zero_engine_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E (zeroEngine coin)
      (RealCoin.law (AlternatingSeries.meanBias parameters p)) Val.bool := by
  have h := AlternatingSeries.alternatingSeries_distSpec (rT := rT) (GF := GF) E
    parameters ExpIntegralCoefficient.coefficient ExpIntegralCoefficient.coefficient_value p
    coin ExpIntegralCoefficient.callback hcoin (ExpIntegralCoefficient.twp_callback E)
  simpa [zeroEngine, ExpIntegralCoefficient.callback, FactorialCallback.factorial, Exp.close,
    Exp.closeRec, Var.internal.injEq] using h

/-- At zero shift use factorial bounds; positive shifts compose the two source factories. -/
theorem expIntegral_distSpec (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.expIntegral &coin.fst #int (m : ℤ) #())
      (RealCoin.law (bias p m)) Val.bool where
  spec F hF := by
    by_cases hm : m = 0
    · subst m
      iintro Hcredit
      isimp only [bias_zero] at Hcredit
      iterate 8 twp_pure
      ieval (change _ ⊢ tglWp E (zeroEngine coin) _)
      iapply (zero_engine_spec E p coin hcoin).spec F hF $$ Hcredit
    · iintro Hcredit
      isimp only [bias, dite_eq_right hm] at Hcredit
      iapply twp_expIntegral_positive E p m (Nat.pos_of_ne_zero hm) coin hcoin F $$ Hcredit

end specification

end

end SampLib.ExpIntegral
