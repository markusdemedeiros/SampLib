import SampLib.Bernoulli.EnvelopeFactory
import SampLib.Bernoulli.Laws.BernoulliEndpoints

open ProbLang
open scoped ENNReal

namespace ExactEnvelopeAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
open SampLib.EnvelopeFactory

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem adaptive_frame (E : CoPset) (a : Parameters) (r : a.toCoefficients.Realization)
    (p : unitInterval) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (a.target p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &coin.fst &bounds.fst &next.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := envelopeFactoryDegrees_distSpec E a r p coin bounds next hcoin hbounds hnext
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

theorem consecutive_frame (E : CoPset) (a : Parameters) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (p : unitInterval) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (a.target p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := envelopeFactory_distSpec E a r ha p coin bounds hcoin hbounds
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

def trueInfinity (b : Bool) : ℝ≥0∞ := if b then ∞ else 0
def falseInfinity (b : Bool) : ℝ≥0∞ := if b then 0 else ∞

example (E : CoPset) (a : Parameters) (r : a.toCoefficients.Realization)
    (p : unitInterval) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next)
    (hz : a.target p = 0) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (trueInfinity b) ∗ I)) := by
  have h := adaptive_frame E a r p coin bounds next hcoin hbounds hnext trueInfinity I
  simpa only [hz, RealCoin.lintegral_law, RealCoin.credit_zero, trueInfinity,
    Bool.false_eq_true, ite_false] using h

example (E : CoPset) (a : Parameters) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (p : unitInterval) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hz : a.target p = 1) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (falseInfinity b) ∗ I)) := by
  have h := consecutive_frame E a r ha p coin bounds hcoin hbounds falseInfinity I
  simpa only [hz, RealCoin.lintegral_law, RealCoin.credit_one, falseInfinity, ite_true] using h

#print axioms SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec
#print axioms SampLib.EnvelopeFactory.envelopeFactory_distSpec
#print axioms SampLib.EnvelopeFactory.Parameters.limit_expectation
#print axioms SampLib.EnvelopeFactory.Parameters.exists_horizon
#print axioms SampLib.EnvelopeFactory.Scheme.thresholds_mean
#print axioms SampLib.EnvelopeFactory.Coefficients.stateMass_transport
#print axioms SampLib.EnvelopeFactory.Coefficients.oldWidth_positive
#print axioms SampLib.EnvelopeFactory.twp_round_prefix
#print axioms SampLib.EnvelopeFactory.twp_compare
#print axioms SampLib.EnvelopeFactory.twp_rescale

end

end ExactEnvelopeAuthorCallers
