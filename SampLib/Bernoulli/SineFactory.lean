import SampLib.Bernoulli.FactorialSeriesFactory

/-! # Sine factory by one outer coin and the sinc factorial engine -/

open ProbLang
open scoped ENNReal

namespace SampLib.SineFactory

noncomputable section

def bias (p : unitInterval) : unitInterval := p * FactorialSeriesFactory.bias .sinc p

@[simp] theorem bias_coe (p : unitInterval) : (bias p : ℝ) = Real.sin p := by
  change (p : ℝ) * Real.sinc p = Real.sin p
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  · rw [Real.sinc_of_ne_zero hp]
    field_simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The outer p-coin converts the continuous sinc extension to sin(p). -/
theorem sineFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.sineFactory &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [bias, ← CoinProduct.expectation_preservation p
      (FactorialSeriesFactory.bias .sinc p) F] at Hcredit
    iapply (hcoin.wp (CoinProduct.firstCredit (FactorialSeriesFactory.bias .sinc p) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      simp only [FactorialSeriesFactory.factorialSeriesFactory_openRec,
        FactorialSeriesFactory.factorialSeriesFactory_closeRec]
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      have h := (FactorialSeriesFactory.factorialSeriesFactory_distSpec
        (rT := rT) (GF := GF) E p .sinc coin hcoin).spec F hF
      simp only [FactorialSeries.Mode.code] at h
      iapply h $$ Hcredit

end specification

end

end SampLib.SineFactory
