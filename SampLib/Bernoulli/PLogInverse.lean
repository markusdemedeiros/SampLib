import SampLib.Discrete.Geometric
import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Elementary
import SampLib.Bernoulli.Laws.PLogInverse

/-! # A logarithmic Bernoulli factory

Conditioning on a positive geometric failure count `n` gives success probability
`1/n`. The logarithmic power series evaluates the resulting mixture.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.PLogInverse

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE proof: sample the failure count, then use its reciprocal as a rational bias. -/
theorem twp_pLogInverse (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p hp) F) -∗
      tglWp E pl(&Occil.FactoryExtra.pLogInverse &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pure
  twp_pure
  twp_bind pl(&Occil.geometric &coin.fst #())
  isimp only [← expectation_preservation p hp F] at Hcredit
  iapply ((Geometric.geometric_distSpec E p hp coin hcoin).wp
    (fun n => RealCoin.credit (countBias n) F) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  cases n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n =>
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    twp_pure
    twp_pure
    rw [Nat.cast_add_one]
    isimp only [countBias] at Hcredit
    iapply (RationalCoin.twp_rationalCoin E 1 (n + 1) _ _ _ F) $$ Hcredit

/-- The logarithmic Bernoulli law, for precisely the terminating coin biases. -/
theorem pLogInverse_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.pLogInverse &coin.fst #())
      (RealCoin.law (bias p hp)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_pLogInverse E p hp coin hcoin F)

end specification

end

end SampLib.PLogInverse
