import SampLib.LatentRationalPower
import SampLib.LatentUniformBagCoins

/-! Two powers of one bag retain their joint dependence on its latent uniform. -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.CoinRationalPower.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def call (l : Loc) (a b : ℕ) : Exp rT :=
  pl(&Occil.PSRN.powerCoin &(UniformBagCoins.value l).fst #int (a : ℤ) #int (b : ℤ) #())

private def twice (l : Loc) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) (call l 5 4))) (call l 2 3)

/-- Both returned bits are conditioned on the same latent U, not two independent uniforms. -/
theorem shared_bag (E : CoPset) (l : Loc) (p : List Bool)
    (H : Bool × Bool → ℝ → ℝ≥0∞) (hH : ∀ bits, Measurable (H bits)) (R : IProp GF) :
    iprop(UniformBag.owns l p ∗ ↯ (LatentCoin.credit LatentUniform.model p
      (bias LatentBernoulli.bias 2 3 (by decide))
      (fun a x => LatentCoin.kernel (bias LatentBernoulli.bias 5 4 (by decide))
        (fun b y => H (a, b) y) x)) ∗ R) ⊢
      tglWp E (twice l)
        (fun result : Val rT => iprop(∃ (a b : Bool) (q : List Bool),
          ⌜result = Val.pair (Val.bool a) (Val.bool b) ∧ p <+: q⌝ ∗
          UniformBag.owns l q ∗ ↯ (∫⁻ x, H (a, b) x ∂DyadicPosterior.law q) ∗ R)) := by
  let O : Val rT → List Bool → IProp GF := fun _ q => UniformBag.owns l q
  have hcoin := UniformBagCoins.coinSpec (GF := GF) E l
  have hfirst := powerCoin_latentCoinProgramSpec E LatentUniform.model O
    LatentBernoulli.bias (fun _ => UniformBagCoins.value l) hcoin 2 3 (by decide)
  have hsecond := powerCoin_latentCoinProgramSpec E LatentUniform.model O
    LatentBernoulli.bias (fun _ => UniformBagCoins.value l) hcoin 5 4 (by decide)
  have hmeas a := LatentCoin.measurable_kernel
    (measurable_bias LatentBernoulli.measurable_bias 5 4 (by decide)) (fun b => hH (a, b))
  iintro ⟨Hbag, Hcredit, HR⟩
  twp_bind (call l 2 3)
  iapply hfirst.wp (.loc l) p
    (fun a x => LatentCoin.kernel (bias LatentBernoulli.bias 5 4 (by decide))
      (fun b y => H (a, b) y) x) hmeas _ $$ Hbag Hcredit
  iintro %a %q %hpq Hbag Hcredit
  have hcredit : (∫⁻ x, LatentCoin.kernel (bias LatentBernoulli.bias 5 4 (by decide))
      (fun b y => H (a, b) y) x ∂LatentUniform.model.posterior q) =
      LatentCoin.credit LatentUniform.model q (bias LatentBernoulli.bias 5 4 (by decide))
        (fun b y => H (a, b) y) := rfl
  isimp only [hcredit] at Hcredit
  twp_pure
  twp_bind (call l 5 4)
  iapply hsecond.wp (.loc l) q (fun b y => H (a, b) y) (fun b => hH (a, b)) _ $$ Hbag Hcredit
  iintro %b %t %hqt Hbag Hcredit
  twp_pures
  twp_value
  imodintro
  iexists a, b, t
  iframe Hbag Hcredit HR
  ipureintro
  exact ⟨rfl, hpq.trans hqt⟩

#print axioms shared_bag
#print axioms powerCoin_latentCoinProgramSpec
#print axioms CoinFractionalPower.fractionalPower_latentCoinProgramSpec
#print axioms CoinIteration.iterateCoin_latentCoinProgramSpec

end

end SampLib.LatentReal.CoinRationalPower.ProducerCallers
