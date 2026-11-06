import SampLib.Bernoulli.EnvelopeFactory
import SampLib.Uniform.FairCoin
import SampLib.Bernoulli.Laws.BernoulliEndpoints

/-! Team `factories` caller: framed resources, fair-coin composition, endpoint laws. -/

open ProbLang
open scoped ENNReal

namespace FactoriesCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
open SampLib.EnvelopeFactory

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Any Bernoulli spec preserves an arbitrary framed resource. -/
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ] (h : IsDistSpec (GF := GF) E e μ Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗
      tglWp E e (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

private def fair : Val rT := ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩

/-- The general factory driven by the verified fair coin. -/
example (E : CoPset) (a : Parameters VonNeumann.fairBias)
    (r : a.toCoefficients.Realization) (bounds next : Val rT)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law a.target) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &Occil.fairCoin &bounds.fst &next.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (envelopeFactoryDegrees_distSpec E VonNeumann.fairBias a r fair bounds next
    (FairCoin.fairCoin_distSpec E) hbounds hnext) F I

/-- The consecutive wrapper driven by the verified fair coin. -/
example (E : CoPset) (a : Parameters VonNeumann.fairBias) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (bounds : Val rT)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law a.target) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactory &Occil.fairCoin &bounds.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (envelopeFactory_distSpec E VonNeumann.fairBias a r ha fair bounds
    (FairCoin.fairCoin_distSpec E) hbounds) F I

/-- Only convergence at the input bias is assumed: raw coefficients and limit at `p`. -/
example (E : CoPset) (p : unitInterval) (c : Coefficients) (target : unitInterval)
    (hlo : Filter.Tendsto (fun t => c.lowerMean t p) Filter.atTop (nhds (target : ℝ)))
    (hhi : Filter.Tendsto (fun t => c.upperMean t p) Filter.atTop (nhds (target : ℝ)))
    (r : c.Realization) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E c r bounds) (hnext : NextSpec (GF := GF) E c next) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #()) (RealCoin.law target) Val.bool :=
  envelopeFactoryDegrees_distSpec E p ⟨c, target, hlo, hhi⟩ r coin bounds next hcoin
    hbounds hnext

def trueInfinity (b : Bool) : ℝ≥0∞ := if b then ∞ else 0
def falseInfinity (b : Bool) : ℝ≥0∞ := if b then 0 else ∞

/-- Input bias `p = 0` is in the domain; a zero target pays nothing on the null `true` event. -/
example (E : CoPset) (a : Parameters 0) (r : a.toCoefficients.Realization)
    (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next)
    (hz : a.target = 0) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (trueInfinity b) ∗ I)) := by
  have h := frame (GF := GF) (envelopeFactoryDegrees_distSpec E 0 a r coin bounds next hcoin hbounds
    hnext) trueInfinity I
  simpa only [hz, RealCoin.lintegral_law, RealCoin.credit_zero, trueInfinity,
    Bool.false_eq_true, ite_false] using h

/-- Input bias `p = 1` with a unit target: the null `false` event may carry infinite credit. -/
example (E : CoPset) (a : Parameters 1) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hz : a.target = 1) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (falseInfinity b) ∗ I)) := by
  have h := frame (GF := GF) (envelopeFactory_distSpec E 1 a r ha coin bounds hcoin hbounds)
    falseInfinity I
  simpa only [hz, RealCoin.lintegral_law, RealCoin.credit_one, falseInfinity, ite_true] using h

end

end FactoriesCallers

#print axioms SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec
#print axioms SampLib.EnvelopeFactory.envelopeFactory_distSpec
