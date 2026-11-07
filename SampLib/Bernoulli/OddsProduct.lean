import SampLib.Core.Retry
import SampLib.Bernoulli.Laws.BernoulliRetry
import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Rational
import Metrology.Iris.LocalBI

/-! # Multiplication of Bernoulli odds

A selector stops with `false`, or tries the input and retries on its failure.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.OddsProduct

noncomputable section

/-- Success probability of a trial conditioned on exiting. -/
abbrev bias (p μ : unitInterval) :=
  BernoulliRetry.bias ((μ : ℝ) * p) (1 - (μ : ℝ))
    (mul_nonneg μ.2.1 p.2.1) (sub_nonneg.mpr μ.2.2)

/-- Retry probability of one selector/input pair. -/
def retry (p μ : unitInterval) : unitInterval :=
  ⟨(μ : ℝ) * (1 - (p : ℝ)), mul_nonneg μ.2.1 (sub_nonneg.mpr p.2.2), by
    calc
      _ ≤ 1 * (1 - (p : ℝ)) :=
        mul_le_mul_of_nonneg_right μ.2.2 (sub_nonneg.mpr p.2.2)
      _ ≤ 1 := by linarith [p.2.1]⟩

private theorem retry_lt_one (p μ : unitInterval) (h : (μ : ℝ) < 1 ∨ 0 < (p : ℝ)) :
    (retry p μ : ℝ) < 1 := by
  rcases h with hμ | hp
  · calc
      _ ≤ (μ : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith [p.2.1]) μ.2.1
      _ < 1 := by simpa using hμ
  · calc
      _ ≤ 1 * (1 - (p : ℝ)) :=
        mul_le_mul_of_nonneg_right μ.2.2 (sub_nonneg.mpr p.2.2)
      _ < 1 := by linarith

/-- Credit after the selected input coin. -/
def coinCredit (p μ : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit (bias p μ) F + BernoulliRetry.factor (retry p μ) * ε

/-- Credit after the selector. -/
def selectorCredit (p μ : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ c, coinCredit p μ F ε c ∂RealCoin.law p else F false

/-- One trial has success mass `μ*p`, failure mass `1-μ`, and retry mass `μ*(1-p)`. -/
theorem expectation (p μ : unitInterval) (h : (μ : ℝ) < 1 ∨ 0 < (p : ℝ))
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, selectorCredit p μ F ε b ∂RealCoin.law μ ≤ RealCoin.credit (bias p μ) F + ε := by
  calc
    _ = ofReal ((μ : ℝ) * p) * F true + ofReal (1 - (μ : ℝ)) * F false +
        ofReal (retry p μ : ℝ) *
          (RealCoin.credit (bias p μ) F + BernoulliRetry.factor (retry p μ) * ε) := by
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, selectorCredit,
        coinCredit, ite_true, Bool.false_eq_true, ite_false, retry, ofReal_mul μ.2.1]
      ring
    _ ≤ _ := BernoulliRetry.expectation _ _ (mul_nonneg μ.2.1 p.2.1)
      (sub_nonneg.mpr μ.2.2) (retry p μ) (retry_lt_one p μ h) (by dsimp [retry]; ring) F ε

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The complete terminating domain excludes only selector one with input zero. -/
theorem twp_oddsProduct (E : CoPset) (p μ : unitInterval)
    (h : (μ : ℝ) < 1 ∨ 0 < (p : ℝ)) (coin selector : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hselector : IsDistSpec (GF := GF) E pl(&selector.fst #()) (RealCoin.law μ) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p μ) F) -∗
      tglWp E pl(&Occil.FactoryExtra.oddsProduct &coin.fst &selector.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply Retry.twp_loop solve_not_value
    (BernoulliRetry.one_lt_factor (retry p μ) (retry_lt_one p μ h))
  iintro !> %ε %hε IH Hcredit
  twp_pures
  twp_bind pl(&selector.fst #())
  ihave Hcredit := ErrorCredit.weaken (expectation p μ h F ε) $$ Hcredit
  iapply (hselector.wp (selectorCredit p μ F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [selectorCredit, ite_true] at Hcredit
    iapply (hcoin.wp (coinCredit p μ F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_bind pl(&Occil.FactoryExtra.oddsProduct &coin.fst &selector.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed law with bias `μ*p/(1-μ+μ*p)`. -/
theorem oddsProduct_distSpec (E : CoPset) (p μ : unitInterval)
    (h : (μ : ℝ) < 1 ∨ 0 < (p : ℝ)) (coin selector : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hselector : IsDistSpec (GF := GF) E pl(&selector.fst #()) (RealCoin.law μ) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.oddsProduct &coin.fst &selector.fst #())
      (RealCoin.law (bias p μ)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_oddsProduct E p μ h coin selector hcoin hselector F)

end specification

end

end SampLib.OddsProduct
