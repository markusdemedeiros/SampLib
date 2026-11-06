import SampLib.Templates
import SampLib.Uniform.RealCoin
import SampLib.Uniform.FairCoin
import SampLib.Bernoulli.OneDivTwoMinus
import SampLib.Bernoulli.ReciprocalLogistic
import SampLib.Bernoulli.IntegralMixture
import SampLib.Bernoulli.PositivePowerSeries
import SampLib.Bernoulli.ComplementLogInverse
import SampLib.Bernoulli.ConvexCombination
import SampLib.Bernoulli.OddsProduct
import SampLib.Bernoulli.ComplementPowerSeries
import SampLib.Constants.FromDigits
import SampLib.Bernoulli.ExpMinusRational
import SampLib.Bernoulli.ApproximateFactory
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal

namespace ExpansionFactoriesReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (OneDivTwoMinus.bias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.oneDivTwoMinus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (OneDivTwoMinus.oneDivTwoMinus_distSpec E p coin hcoin) F I

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ c, F c ∂RealCoin.law (ReciprocalLogistic.bias p a b ha hb)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.reciprocalLogistic &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ c : Bool, ⌜v = Val.bool c⌝ ∗ ↯ (F c) ∗ I)) :=
  frame (ReciprocalLogistic.reciprocalLogistic_distSpec E p a b ha hb coin hcoin) F I

example : (OneDivTwoMinus.bias 0 : ℝ) = 1 / 2 := by
  norm_num [OneDivTwoMinus.bias_coe]

example : (OneDivTwoMinus.bias 1 : ℝ) = 1 := by
  norm_num [OneDivTwoMinus.bias_coe]

example (p : unitInterval) : (ReciprocalLogistic.bias p 0 3 (by norm_num)
    (by norm_num) : ℝ) = 1 := by
  norm_num [ReciprocalLogistic.bias]

example : (ReciprocalLogistic.bias 1 2 3 (by norm_num) (by norm_num) : ℝ) = 3 / 5 := by
  norm_num [ReciprocalLogistic.bias]

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂RealCoin.law (OneDivTwoMinus.bias 1)) = 0 := by
  norm_num [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, OneDivTwoMinus.bias_coe]

example (p : unitInterval) : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂RealCoin.law (ReciprocalLogistic.bias p 0 3 (by norm_num) (by norm_num))) = 0 := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, ReciprocalLogistic.bias]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.oneDivTwoMinus &Occil.fairCoin #())
      (RealCoin.law (OneDivTwoMinus.bias VonNeumann.fairBias)) Val.bool :=
  OneDivTwoMinus.oneDivTwoMinus_distSpec E VonNeumann.fairBias
    ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩ (FairCoin.fairCoin_distSpec E)

#print axioms OneDivTwoMinus.oneDivTwoMinus_distSpec
#print axioms OneDivTwoMinus.twp_oneDivTwoMinus
#print axioms OneDivTwoMinus.bias_coe
#print axioms ReciprocalLogistic.reciprocalLogistic_distSpec
#print axioms ReciprocalLogistic.twp_reciprocalLogistic
#print axioms ReciprocalLogistic.expectation

example {α : Type _} [MeasurableSpace α] (E : CoPset)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (κ : α → MeasureTheory.Measure Bool) [∀ x, MeasureTheory.IsProbabilityMeasure (κ x)]
    (hκ : Measurable κ) (encode : α → Val rT) (parameter factory : Val rT)
    (hparameter : IsDistSpec (GF := GF) E pl(&parameter.fst #()) μ encode)
    (hfactory : ∀ x, IsDistSpec (GF := GF) E
      pl(&factory.fst &(encode x).fst #()) (κ x) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂IntegralMixture.law μ κ) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.integralMixture &parameter.fst &factory.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have := IntegralMixture.law_probability μ κ hκ
  exact frame (IntegralMixture.integralMixture_distSpec E μ κ hκ encode parameter factory
    hparameter hfactory) F I

example (p : unitInterval) :
    (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
      ∂IntegralMixture.law (RealCoin.law p) (fun _ => RealCoin.law 1)) = 0 := by
  rw [← IntegralMixture.expectation _ _ measurable_const]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

#print axioms IntegralMixture.integralMixture_distSpec
#print axioms IntegralMixture.twp_integralMixture
#print axioms IntegralMixture.expectation

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂PositivePowerSeries.law p ws) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.positivePowerSeries &coin.fst
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (PositivePowerSeries.positivePowerSeries_distSpec E p coin hcoin ws) F I

example :
    letI : NeZero ([1, 1] : List ℕ).sum := ⟨by decide⟩
    PositivePowerSeries.law 0 [1, 1] {true} = 1 / 2 := by
  norm_num [PositivePowerSeries.success_probability, WeightedChoice.weightedSum]

example :
    letI : NeZero ([0, 2] : List ℕ).sum := ⟨by decide⟩
    (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞) ∂PositivePowerSeries.law 0 [0, 2]) = 0 := by
  simp only [PositivePowerSeries.law]
  rw [← ProbabilityGeneratingFactory.expectation_preservation, WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, IterateCoin.credit, IterateCoin.bias,
    RealCoin.credit, RealCoin.pmf]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval)
    (hp : (p : ℝ) < 1) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ComplementLogInverse.bias p hp)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.complementLogInverse &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (ComplementLogInverse.complementLogInverse_distSpec E p hp coin hcoin) F I

example : (ComplementLogInverse.bias 0 (by norm_num) : ℝ) = 0 := by
  simp [ComplementLogInverse.bias_coe]

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂RealCoin.law (ComplementLogInverse.bias 0 (by norm_num))) = 0 := by
  norm_num [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    ComplementLogInverse.bias_coe]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (ws : List ℕ) [NeZero ws.sum]
    (p : ℕ → unitInterval) (coins : List (Val rT)) (hlen : coins.length = ws.length)
    (hcoins : ∀ i : Fin coins.length, IsDistSpec (GF := GF) E
      pl(&(coins.get i).fst #()) (RealCoin.law (p i)) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂ConvexCombination.law ws p) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.convexCombination
        &(listVal (fun n : ℕ => Val.int n) ws).fst &(listVal id coins).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (ConvexCombination.convexCombination_distSpec E ws p coins hlen hcoins) F I

example : ConvexCombination.law [1, 1] (fun i => if i = 0 then 0 else 1) {true} = 1 / 2 := by
  norm_num [ConvexCombination.success_probability, WeightedChoice.weightedSum]

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂ConvexCombination.law [0, 2, 0] (fun _ => 1)) = 0 := by
  rw [← ConvexCombination.expectation, WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, ConvexCombination.componentCredit,
    RealCoin.credit, RealCoin.pmf]

example (E : CoPset) (p μ : unitInterval) (h : (μ : ℝ) < 1 ∨ 0 < (p : ℝ))
    (coin selector : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hselector : IsDistSpec (GF := GF) E pl(&selector.fst #()) (RealCoin.law μ) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (OddsProduct.bias p μ)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.oddsProduct &coin.fst &selector.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (OddsProduct.oddsProduct_distSpec E p μ h coin selector hcoin hselector) F I

example (p : unitInterval) : (OddsProduct.bias p 0 : ℝ) = 0 := by
  simp [OddsProduct.bias, BernoulliRetry.bias]

example (p : unitInterval) (hp : 0 < (p : ℝ)) : (OddsProduct.bias p 1 : ℝ) = 1 := by
  simp [OddsProduct.bias, BernoulliRetry.bias, hp.ne']

example (p : unitInterval) : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂RealCoin.law (OddsProduct.bias p 0)) = 0 := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    OddsProduct.bias, BernoulliRetry.bias]

#print axioms PositivePowerSeries.positivePowerSeries_distSpec
#print axioms PositivePowerSeries.success_probability
#print axioms ComplementLogInverse.complementLogInverse_distSpec
#print axioms ComplementLogInverse.bias_coe
#print axioms ConvexCombination.convexCombination_distSpec
#print axioms ConvexCombination.expectation
#print axioms ConvexCombination.success_probability
#print axioms OddsProduct.oddsProduct_distSpec
#print axioms OddsProduct.expectation
#print axioms BernoulliRetry.expectation
#print axioms CoinComplement.distSpec

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂ComplementPowerSeries.law p ws) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.complementPowerSeries &coin.fst
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (ComplementPowerSeries.complementPowerSeries_distSpec E p coin hcoin ws) F I

example (p : unitInterval) : ComplementPowerSeries.law p [1] {true} = ENNReal.ofReal p := by
  simp [ComplementPowerSeries.success_probability, WeightedChoice.weightedSum]

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂ComplementPowerSeries.law 1 [0, 2]) = 0 := by
  rw [← ComplementPowerSeries.expectation, WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, ComplementPowerSeries.continuation,
    IterateCoin.credit, IterateCoin.bias, RealCoin.credit, RealCoin.pmf,
    unitInterval.coe_symm_eq]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (b : ℕ) (hb : 1 < b)
    (d : ℕ → Fin b) (digit : Val rT)
    (hdigit : ∀ k : ℕ, ⊢ tglWp E pl(&digit.fst #int ((k + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (d k : ℤ)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ a, F a ∂RealCoin.law (FromDigits.bias d 0)) ∗ I -∗
      tglWp E pl(&Occil.Constants.fromDigits #int (b : ℤ) &digit.fst #())
        (fun v : Val rT => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a) ∗ I)) :=
  frame (FromDigits.fromDigits_distSpec E b hb d digit hdigit) F I

example : (FromDigits.bias (fun _ => (0 : Fin 2)) 0 : ℝ) = 0 := by
  simp [FromDigits.bias, Real.ofDigits, Real.ofDigitsTerm]

private theorem last_bias : (FromDigits.bias (fun _ => Fin.last 1) 0 : ℝ) = 1 := by
  change Real.ofDigits (fun _ => Fin.last 1) = 1
  exact Real.ofDigits_const_last_eq_one 1

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂RealCoin.law (FromDigits.bias (fun _ => (0 : Fin 2)) 0)) = 0 := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    FromDigits.bias, Real.ofDigits, Real.ofDigitsTerm]

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂RealCoin.law (FromDigits.bias (fun _ => Fin.last 1) 0)) = 0 := by
  have h : FromDigits.bias (fun _ => Fin.last 1) 0 = 1 := Subtype.ext last_bias
  rw [h]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ c, F c ∂RealCoin.law (ExpMinusRational.bias a b ha hb)) ∗ I -∗
      tglWp E pl(&Occil.expMinusRational #int a #int b #())
        (fun v : Val rT => iprop(∃ c : Bool, ⌜v = Val.bool c⌝ ∗ ↯ (F c) ∗ I)) :=
  frame (ExpMinusRational.expMinusRational_distSpec E a b ha hb) F I

example : (ExpMinusRational.bias 0 3 (by norm_num) (by norm_num) : ℝ) = 1 := by
  simp [ExpMinusRational.bias]

example : (ExpMinusRational.bias 6 3 (by norm_num) (by norm_num) : ℝ) = Real.exp (-2) := by
  norm_num [ExpMinusRational.bias]

example : (ExpMinusRational.bias 3 2 (by norm_num) (by norm_num) : ℝ) =
    Real.exp (-1) * Real.exp (-(1 / 2)) := by
  rw [← Real.exp_add]
  norm_num [ExpMinusRational.bias]

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂RealCoin.law (ExpMinusRational.bias 0 3 (by norm_num) (by norm_num))) = 0 := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, ExpMinusRational.bias]

#print axioms ComplementPowerSeries.complementPowerSeries_distSpec
#print axioms ComplementPowerSeries.expectation
#print axioms ComplementPowerSeries.success_probability
#print axioms FromDigits.fromDigits_distSpec
#print axioms FromDigits.twp_fromDigits
#print axioms FromDigits.expectation
#print axioms Real.ofDigits_cons
#print axioms ExpMinusRational.expMinusRational_distSpec
#print axioms ExpMinusRational.twp_expMinusRational
#print axioms AlternatingFactorial.credit_one

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval)
    (coin evaluate : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (trials scale : ℕ) [NeZero trials] [NeZero scale] (f : ℤ → ℤ)
    (hevaluate : ∀ k : Fin (trials + 1),
      ⊢ tglWp E pl(&evaluate.fst #int (scale : ℤ)
        #int ((scale : ℤ) * (k : ℕ) / trials))
        (fun v : Val rT => iprop(⌜v = Val.int (f ((scale : ℤ) * (k : ℕ) / trials))⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂ApproximateFactory.law p trials scale f) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.approximateFactory &coin.fst #int (trials : ℤ)
        #int (scale : ℤ) &evaluate.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (ApproximateFactory.approximateFactory_distSpec E p coin evaluate hcoin trials scale f
    hevaluate) F I

example (p : unitInterval) : ApproximateFactory.law p 2 1 id {true} =
    ENNReal.ofReal ((p : ℝ) ^ 2) := by
  norm_num [ApproximateFactory.success_probability, Finset.sum_range_succ,
    ApproximateFactory.componentBias, ApproximateFactory.clamp, RationalCoin.bias]

example (p : unitInterval) : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂ApproximateFactory.law p 2 1 (fun _ => -3)) = 0 := by
  rw [ApproximateFactory.law,
    MeasureTheory.Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    ApproximateFactory.componentBias, ApproximateFactory.clamp, RationalCoin.bias]

example (p : unitInterval) : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂ApproximateFactory.law p 2 1 (fun _ => 3)) = 0 := by
  rw [ApproximateFactory.law,
    MeasureTheory.Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    ApproximateFactory.componentBias, ApproximateFactory.clamp, RationalCoin.bias]

#print axioms ApproximateFactory.approximateFactory_distSpec
#print axioms ApproximateFactory.expectation
#print axioms ApproximateFactory.success_probability

end

end ExpansionFactoriesReview
