import SampLib.Samplers.CoinConditional
import SampLib.Samplers.Complement
import SampLib.Distributions.BernoulliEndpoints

/-! # Composing Bernoulli specifications for expression trees -/

open ProbLang
open scoped ENNReal

namespace SampLib.CoinExpression

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem conditional (E : CoPset) (p q r : unitInterval) (left right select : Exp rT)
    (hleft : IsDistSpec (GF := GF) E left (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E right (RealCoin.law q) Val.bool)
    (hselect : IsDistSpec (GF := GF) E select (RealCoin.law r) Val.bool) :
    IsDistSpec (GF := GF) E (.cond select left right)
      (RealCoin.law (CoinConditional.bias p q r)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_bind select
    isimp only [← CoinConditional.expectation_preservation p q r F] at Hcredit
    iapply (hselect.wp (CoinConditional.firstCredit p q F) (measurable_of_countable _) _) $$
      Hcredit
    iintro %a Hcredit
    cases a
    · twp_pure
      isimp only [CoinConditional.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iapply hright.spec F hF $$ Hcredit
    · twp_pure
      isimp only [CoinConditional.firstCredit, ite_true] at Hcredit
      iapply hleft.spec F hF $$ Hcredit

theorem negate (E : CoPset) (p : unitInterval) (coin : Exp rT)
    (hcoin : IsDistSpec (GF := GF) E coin (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E (.unop .neg coin)
      (RealCoin.law (unitInterval.symm p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_bind coin
    isimp only [← Complement.expectation_preservation p F] at Hcredit
    iapply (hcoin.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b <;> twp_pure <;> twp_value <;> imodintro
    · iexists true
      isimp only [Bool.not_false] at Hcredit
      iframe Hcredit
      itrivial
    · iexists false
      isimp only [Bool.not_true] at Hcredit
      iframe Hcredit
      itrivial

theorem false_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(#false) (RealCoin.law 0) Val.bool where
  spec F _ := by
    simp only [RealCoin.lintegral_law, RealCoin.credit_zero]
    iintro Hcredit
    twp_value
    imodintro
    iexists false
    iframe Hcredit
    itrivial

end

end SampLib.CoinExpression
