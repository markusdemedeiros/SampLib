import SampLib.Common.FactorySyntax
import Samplers.Bernoulli.Powers

/-! # The integer-exponent branch of the rational power factory

This supporting rule executes the original quotient/remainder dispatch. A zero
remainder never calls the fractional-power engine.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RationalPowerInteger

noncomputable section

private def source {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.rationalPower, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.FactoryExtra.rationalPower := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- An integer exponent takes only the independently verified all-successes branch. -/
theorem rationalPower_integer_distSpec (E : CoPset) (p : unitInterval)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n b : ℕ) (hb : 0 < b) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.rationalPower &coin.fst #int ((n * b : ℕ) : ℤ)
        #int (b : ℤ) #()) (IterateCoin.law p n) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    twp_pures
    have hbz : (0 : ℤ) < b := by exact_mod_cast hb
    have hguard : decide ((b : ℤ) ≤ 0) = false := by
      simp only [decide_eq_false_iff_not, not_le]
      exact hbz
    simp only [Nat.cast_mul, hguard, Bool.false_or, FactorySyntax.iterateCoin_openRec,
      FactorySyntax.iterateCoin_closeRec]
    twp_pure
    twp_pure
    rw [Int.mul_ediv_cancel _ hbz.ne']
    twp_bind pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
    iapply (IterateCoin.iterateCoin_distSpec E p coin hcoin n).wp F
      (measurable_of_countable _) _ $$ Hcredit
    iintro %bit Hcredit
    cases bit
    · twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial
    · twp_pures
      rw [Int.mul_emod_left]
      twp_pures
      twp_value
      imodintro
      iexists true
      iframe Hcredit
      itrivial

end specification

end

end SampLib.RationalPowerInteger
