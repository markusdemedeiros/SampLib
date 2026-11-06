import SampLib.Samplers.LogRatioFactories

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.ExactLogRatioCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed_complement (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (LogRatioFactories.complementBias p hp))) ⊢
      tglWp E pl(&Occil.FactoryExtra.complementOverLogInverse &coin.fst #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((LogRatioFactories.complementOverLogInverse_distSpec E p hp coin hcoin).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

theorem framed_overLog (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (LogRatioFactories.overLogBias p hp))) ⊢
      tglWp E pl(&Occil.FactoryExtra.pOverLogInverseComplement &coin.fst #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((LogRatioFactories.pOverLogInverseComplement_distSpec E p hp coin hcoin).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

/-- Sequence two uses without closing over an arbitrary callback's free variables. -/
private def observeAgain (base exponent : Val rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) (.app exponent.fst (.lit .unit))))
    pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())

/-- Observing the same oracle after the factory retains the original shared latent law. -/
theorem shared_observation (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (H : Bool → Bool → ℝ → ℝ≥0∞)
    (hH : ∀ first second, Measurable (H first second)) (P : IProp GF) :
    iprop(P ∗ UniformBag.owns l q ∗ ↯ (LatentBernoulli.credit q
      (fun u => FractionalPower.powerBias p (φ u))
      (fun first => LatentBernoulli.kernel φ (H first)))) ⊢
      tglWp E (observeAgain base exponent) (fun v : Val rT => iprop(
        ∃ (first second : Bool) (r : List Bool),
          ⌜v = Val.pair (Val.bool first) (Val.bool second) ∧ q <+: r⌝ ∗
            P ∗ UniformBag.owns l r ∗ ↯ (DyadicPosterior.credit r (H first second)))) := by
  iintro ⟨HP, Hbag, Hcredit⟩
  unfold observeAgain
  twp_bind pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
  iapply ((LatentPower.twoCoinPower_coinSpec E p hp φ base exponent l hbase hexponent).wp
    q (fun first => LatentBernoulli.kernel φ (H first))
    (fun first => LatentBernoulli.measurable_kernel hexponent.measurable_bias (hH first)) _) $$
      Hbag Hcredit
  iintro %first %q' %hq Hbag Hcredit
  twp_pure
  twp_bind pl(&exponent.fst #())
  ihave Hcoin : ↯ (LatentBernoulli.credit q' φ (H first)) $$ [Hcredit]
  · isimp only [LatentBernoulli.credit]
    iexact Hcredit
  iapply (hexponent.wp q' (H first) (hH first) _) $$ Hbag Hcoin
  iintro %second %r %hr Hbag Hcredit
  twp_pures
  twp_value
  imodintro
  iexists first, second, r
  iframe HP Hbag Hcredit
  ipureintro
  exact ⟨rfl, hq.trans hr⟩

#print axioms LogRatioFactories.complementOverLogInverse_distSpec
#print axioms LogRatioFactories.pOverLogInverseComplement_distSpec
#print axioms LatentPower.twoCoinPower_coinSpec
#print axioms framed_complement
#print axioms framed_overLog
#print axioms shared_observation

end

end SampLib.ExactLogRatioCallers
