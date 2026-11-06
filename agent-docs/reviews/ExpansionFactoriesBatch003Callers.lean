import SampLib.Samplers.Polylogarithm
import SampLib.Samplers.AlgebraicRoot
import SampLib.Samplers.InverseGoldenRatio
import SampLib.Samplers.SigmoidRational
import SampLib.Samplers.SigmoidDerivative
import SampLib.Samplers.LogisticExp
import SampLib.Samplers.ExponentialRatio
import SampLib.Samplers.TanhRational
import SampLib.Distributions.BernoulliMixture
import SampLib.Templates
import SampLib.Samplers.RealCoin
import SampLib.Samplers.FairCoin
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

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval)
    (hp : (p : ℝ) < 1) (order : ℕ) (ho : 0 < order) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂Polylogarithm.law p order) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.polylogarithm &coin.fst #int (order : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (Polylogarithm.polylogarithm_distSpec E p hp order ho coin hcoin) F I

private theorem polylog_zero (order : ℕ) : Polylogarithm.law 0 order {true} = 1 := by
  rw [Polylogarithm.success_probability 0 (by norm_num)]
  simp [zero_pow_eq, ite_div, apply_ite]

example (order : ℕ) : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂Polylogarithm.law 0 order) = 0 := by
  have h : Polylogarithm.law 0 order = RealCoin.law 1 :=
    BernoulliMixture.eq_bernoulli_of_apply_true _ 1 (by simpa using polylog_zero order)
  rw [h]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.intPower #0 #0)
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  simpa using FactoryIntegerPower.twp_intPower (rT := rT) (GF := GF) E 0 0

example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.intPower #(-2) #3)
      (fun v : Val rT => iprop(⌜v = Val.int (-8)⌝)) := by
  simpa using FactoryIntegerPower.twp_intPower (rT := rT) (GF := GF) E (-2) 3

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (oracle : Val rT)
    (horacle : ∀ n den : ℕ, n ≤ den → 0 < den →
      ⊢ tglWp E pl(&oracle.fst #int (n : ℤ) #int (den : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.int (AlgebraicRoot.side p s n den)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law p) ∗ I -∗
      tglWp E pl(&Occil.Constants.algebraicRoot &oracle.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (AlgebraicRoot.algebraicRoot_distSpec E p hp0 hp1 s hs oracle horacle) F I

example (s : ℤ) : AlgebraicRoot.side VonNeumann.fairBias s 1 2 = 0 := by
  norm_num [AlgebraicRoot.side, VonNeumann.fairBias]

example : AlgebraicRoot.side VonNeumann.fairBias 1 0 1 = 1 := by
  norm_num [AlgebraicRoot.side, VonNeumann.fairBias]

example : AlgebraicRoot.side VonNeumann.fairBias (-1) 0 1 = -1 := by
  norm_num [AlgebraicRoot.side, VonNeumann.fairBias]

example (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    AlgebraicRoot.bitCredit (AlgebraicRoot.Cell.initial VonNeumann.fairBias) F ε 0 = F true := by
  norm_num [AlgebraicRoot.bitCredit, AlgebraicRoot.Cell.initial,
    AlgebraicRoot.Cell.probability, VonNeumann.fairBias]

example (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    AlgebraicRoot.bitCredit (AlgebraicRoot.Cell.initial VonNeumann.fairBias) F ε 1 = F false := by
  norm_num [AlgebraicRoot.bitCredit, AlgebraicRoot.Cell.initial,
    AlgebraicRoot.Cell.probability, VonNeumann.fairBias]

example (E : CoPset) [ProbLangDist.IsUniformInt rT]
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law InverseGoldenRatio.bias) ∗ I -∗
      tglWp E pl(&Occil.Constants.inverseGoldenRatio #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (InverseGoldenRatio.inverseGoldenRatio_distSpec E) F I

example : (InverseGoldenRatio.bias : ℝ) = Real.goldenRatio⁻¹ := rfl

example : AlgebraicRoot.side InverseGoldenRatio.bias 1 1 2 = 1 := by
  have h := InverseGoldenRatio.polynomial_sign 1 2 (by decide)
  norm_num at h
  exact h.symm

example : AlgebraicRoot.side InverseGoldenRatio.bias 1 2 3 = -1 := by
  have h := InverseGoldenRatio.polynomial_sign 2 3 (by decide)
  norm_num at h
  exact h.symm

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b : ℤ) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (SigmoidRational.bias a b)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r) ∗ I)) :=
  frame (SigmoidRational.sigmoidRational_distSpec E a b hb) F I

example (b : ℤ) : (SigmoidRational.bias 0 b : ℝ) = 1 / 2 := by
  norm_num [SigmoidRational.bias]

example : (SigmoidRational.bias (-3) 2 : ℝ) = 1 / (1 + Real.exp (3 / 2)) := by
  norm_num [SigmoidRational.bias]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b : ℤ) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (SigmoidDerivative.bias a b)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.sigmoidDerivative #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r) ∗ I)) :=
  frame (SigmoidDerivative.sigmoidDerivative_distSpec E a b hb) F I

example (b : ℤ) : (SigmoidDerivative.bias 0 b : ℝ) = 1 / 4 := by
  norm_num [SigmoidDerivative.bias, SigmoidRational.bias, unitInterval.coe_symm_eq]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (z : ℤ) (precision : ℕ)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (LogisticExp.bias z precision)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.logisticExp #int z #int (precision : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r) ∗ I)) :=
  frame (LogisticExp.logisticExp_distSpec E z precision) F I

example : (LogisticExp.bias 3 0 : ℝ) = 1 / (1 + Real.exp 3) := by
  norm_num [LogisticExp.coe_bias]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b x y : ℤ)
    (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 < y) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (ExponentialRatio.bias a b x y hx hy)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.exponentialRatio #int a #int b #int x #int y #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r) ∗ I)) :=
  frame (ExponentialRatio.exponentialRatio_distSpec E a b x y hb hx hy) F I

example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂RealCoin.law (ExponentialRatio.bias (-3) 2 0 1 (by norm_num) (by norm_num))) = 0 := by
  have h : ExponentialRatio.bias (-3) 2 0 1 (by norm_num) (by norm_num) = 1 := by
    apply Subtype.ext
    rw [ExponentialRatio.coe_bias]
    simp only [Int.cast_zero, zero_div, sub_zero]
    exact div_self (by positivity)
  rw [h]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (TanhRational.bias a b ha hb)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.tanhRational #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r) ∗ I)) :=
  frame (TanhRational.tanhRational_distSpec E a b ha hb) F I

example (b : ℤ) (hb : 0 < b) : (TanhRational.bias 0 b (by decide) hb : ℝ) = 0 := by
  simp [TanhRational.coe_bias]

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂RealCoin.law (TanhRational.bias 0 1 (by norm_num) (by norm_num))) = 0 := by
  norm_num [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, TanhRational.coe_bias]

#print axioms Polylogarithm.polylogarithm_distSpec
#print axioms Polylogarithm.success_probability
#print axioms FactoryIntegerPower.twp_intPower
#print axioms AlgebraicRoot.algebraicRoot_distSpec
#print axioms AlgebraicRoot.expectation
#print axioms CoinMean.credit_mean
#print axioms InverseGoldenRatio.inverseGoldenRatio_distSpec
#print axioms InverseGoldenRatio.polynomial_sign
#print axioms IntegerSign.twp_integerSign
#print axioms SigmoidRational.sigmoidRational_distSpec
#print axioms SigmoidDerivative.sigmoidDerivative_distSpec
#print axioms SigmoidDerivative.expectation
#print axioms LogisticExp.logisticExp_distSpec
#print axioms ExponentialRatio.exponentialRatio_distSpec
#print axioms ExponentialRatio.expectation
#print axioms TanhRational.tanhRational_distSpec
#print axioms TanhRational.coe_bias
#print axioms BernoulliMixture.expectation

end

end ExpansionFactoriesReview
