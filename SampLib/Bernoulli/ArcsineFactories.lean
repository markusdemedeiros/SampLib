import SampLib.Bernoulli.AlternatingSeries
import SampLib.Bernoulli.FractionalPower
import SampLib.Continuous.IterateCoin
import SampLib.Bernoulli.CoinMean
import SampLib.Bernoulli.CoinProduct
import SampLib.Bernoulli.Complement
import SampLib.Bernoulli.Laws.ArcsineHalf
import SampLib.Bernoulli.Support.ArcsineCoefficients
import SampLib.Bernoulli.Syntax.TrigonometricCallbacks
import Samplers.Bernoulli.Trigonometric

/-! # The two arcsine factories

The central-binomial coefficient engine gives asin(p)+sqrt(1-p²)−1. Mixing with
the complementary square-root coin cancels the square-root term.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ArcsineFactories

noncomputable section

private def coefficientCallback {rT : Type} : Val rT :=
  ⟨ArcsineCoefficients.coefficient, .lam (by is_lc), by is_lc⟩

private def complementSquare {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam pl(~(&Occil.iterateCoin &coin.fst #2)), .lam (by is_lc), by is_lc⟩

private instance choose_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance power_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private instance iterate_closed {rT : Type} : ClosedExp (Occil.iterateCoin : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.iterateCoin, Exp.fv]

private instance alternating_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.alternatingSeries : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.alternatingSeries, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv, ClosedExp.closeRec, ClosedExp.fv]

private instance arcsine_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.arcsinePlusSqrtMinusOne : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.arcsinePlusSqrtMinusOne, Exp.fv,
      ClosedExp.closeRec, ClosedExp.fv]

private instance fractional_closed {rT : Type} : ClosedExp (Occil.fractionalPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.fractionalPower, Occil.rationalCoin, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The source alternating series followed by one outer input coin. -/
theorem arcsinePlusSqrtMinusOne_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.arcsinePlusSqrtMinusOne &coin.fst #())
      (RealCoin.law (ArcsineFactoryParameters.bias p)) Val.bool where
  spec F hF := by
    have hs := AlternatingSeries.alternatingSeries_distSpec E ArcsineFactoryParameters.parameters
      ArcsineCoefficients.raw ArcsineCoefficients.raw_value p coin coefficientCallback hcoin
      (fun n => ArcsineCoefficients.twp_coefficient E n)
    have hnext := hs.spec F hF
    simp only [coefficientCallback] at hnext
    rw [ArcsineCoefficients.coefficient_eq_code] at hnext
    iintro Hcredit
    iterate 2 twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [ArcsineFactoryParameters.bias, ← CoinProduct.expectation_preservation p
      (AlternatingSeries.meanBias ArcsineFactoryParameters.parameters p) F] at Hcredit
    iapply (hcoin.wp
      (CoinProduct.firstCredit (AlternatingSeries.meanBias ArcsineFactoryParameters.parameters p) F)
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
    · iterate 2 twp_pure
      simp only [ClosedExp.openRec, ClosedExp.closeRec]
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      ieval (change _ ⊢ tglWp E (TrigonometricCallbacks.arcsineCall coin.fst) _)
      rw [TrigonometricCallbacks.arcsineCall_eq]
      iapply hnext $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem complementSquare_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(complementSquare coin).fst #())
      (RealCoin.law (unitInterval.symm (p * p))) Val.bool where
  spec F _ := by
    have hs := IterateCoin.iterateCoin_distSpec E p coin hcoin 2
    have hb : IterateCoin.bias p 2 = p * p := Subtype.ext (by
      simp [IterateCoin.bias, pow_two])
    simp only [IterateCoin.law, hb] at hs
    iintro Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    twp_bind pl(&Occil.iterateCoin &coin.fst #2)
    isimp only [← Complement.expectation_preservation (p * p) F] at Hcredit
    iapply (hs.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !b
    iframe Hcredit
    ipureintro
    cases b <;> rfl

/-- The half-arcsine factory is the exact fair mixture, including both input endpoints. -/
theorem arcsineHalf_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.arcsineHalf &coin.fst #())
      (RealCoin.law (halfBias p)) Val.bool where
  spec F hF := by
    have hroot := FractionalPower.fractionalPower_distSpec E (unitInterval.symm (p * p))
      1 2 (by decide) (by decide) (complementSquare coin) (complementSquare_spec E p coin hcoin)
    simp only [complementSquare] at hroot
    iintro Hcredit
    iterate 2 twp_pure
    simp only [FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec]
    twp_bind pl(&Occil.fairCoin #())
    isimp only [halfBias, ← CoinMean.expectation_preservation] at Hcredit
    iapply ((FairCoin.fairCoin_distSpec E).wp
      (CoinConditional.firstCredit (ArcsineFactoryParameters.bias p)
        (unitInterval.symm (rootBias p)) F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      simp only [ClosedExp.openRec, ClosedExp.closeRec]
      twp_bind pl(&Occil.fractionalPower {Exp.lam pl(~(&Occil.iterateCoin &coin.fst #2))} #1 #2 #())
      isimp only [CoinConditional.firstCredit, Bool.false_eq_true, ite_false,
        ← Complement.expectation_preservation (rootBias p) F] at Hcredit
      iapply (hroot.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
      iintro %bit Hcredit
      twp_pures
      twp_value
      imodintro
      iexists !bit
      iframe Hcredit
      ipureintro
      cases bit <;> rfl
    · twp_pure
      simp only [ClosedExp.openRec, ClosedExp.closeRec]
      isimp only [CoinConditional.firstCredit, ite_true] at Hcredit
      iapply (arcsinePlusSqrtMinusOne_distSpec E p coin hcoin).spec F hF $$ Hcredit

end specification

end

end SampLib.ArcsineFactories
