import SampLib.Templates
import SampLib.Samplers.RealCoin
import SampLib.Samplers.FairCoin
import SampLib.Samplers.OneDivTwoMinus
import SampLib.Samplers.ReciprocalLogistic
import SampLib.Samplers.IntegralMixture
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

end

end ExpansionFactoriesReview
