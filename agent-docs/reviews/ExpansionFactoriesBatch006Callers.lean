import SampLib.Bernoulli.TwoCoin
import SampLib.Bernoulli.ExponentialTwist
import SampLib.Bernoulli.ExpMinusScaled
import SampLib.Bernoulli.TanhScaled
import SampLib.Bernoulli.SigmoidScaled
import SampLib.Bernoulli.ExpMinusRational
import SampLib.Templates
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal NNReal

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


variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (p : unitInterval) (x y : ℕ) (hy : 0 < y) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusScaled.expMinusScaled_distSpec E p x y hy coin hc) F I

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TanhScaled.tanhScaled_distSpec E p a b hb coin hc) F I

example (E : CoPset) (p : unitInterval) (a : ℤ) (b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (SigmoidScaled.sigmoidScaled_distSpec E p a b hb coin hc) F I

example (E : CoPset) (p : unitInterval) (a b : ℤ) (hb : 0 < b) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExponentialTwist.exponentialTwist_distSpec E p a b hb coin hc) F I

example (p : unitInterval) (b : ℤ) : ExponentialTwist.bias p 0 b = p := by
  apply Subtype.ext
  rw [ExponentialTwist.coe_bias]
  simp
example (a b : ℤ) : ExponentialTwist.bias 0 a b = 0 := by
  apply Subtype.ext
  rw [ExponentialTwist.coe_bias]
  simp
example (a b : ℤ) : ExponentialTwist.bias 1 a b = 1 := by
  apply Subtype.ext
  rw [ExponentialTwist.coe_bias]
  simp
example (a b : ℤ) : RealCoin.credit (ExponentialTwist.bias 0 a b)
    (fun b => if b then ∞ else 0) = 0 := by
  have h : ExponentialTwist.bias 0 a b = 0 := by
    apply Subtype.ext
    rw [ExponentialTwist.coe_bias]
    simp
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]
example (a b : ℤ) : RealCoin.credit (ExponentialTwist.bias 1 a b)
    (fun b => if b then 0 else ∞) = 0 := by
  have h : ExponentialTwist.bias 1 a b = 1 := by
    apply Subtype.ext
    rw [ExponentialTwist.coe_bias]
    simp
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]

example (E : CoPset) (p q : unitInterval) (x y a b : ℕ)
    (hxy : 0 < x+y) (hb : 0 < b) (hab : a ≤ b)
    (h : 0 < TwoCoin.success p (TwoCoin.weightBias x y hxy) (TwoCoin.portkeyBias a b hb hab) +
      TwoCoin.failure q (TwoCoin.weightBias x y hxy) (TwoCoin.portkeyBias a b hb hab))
    (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TwoCoin.twoCoin_distSpec E p q x y a b hxy hb hab h left right hl hr) F I

example (p q r : unitInterval) : TwoCoin.bias p q r 0 = 0 := by
  apply Subtype.ext
  rw [TwoCoin.bias_coe]
  simp
example (p q β : unitInterval) : TwoCoin.bias p q 0 β = 0 := by
  apply Subtype.ext
  rw [TwoCoin.bias_coe]
  simp
example (q β : unitInterval) : TwoCoin.bias 1 q 1 β = β := by
  apply Subtype.ext
  rw [TwoCoin.bias_coe]
  simp
example (r : unitInterval) : TwoCoin.bias 1 1 r 1 = r := by
  apply Subtype.ext
  rw [TwoCoin.bias_coe]
  simp
example : TwoCoin.success 0 1 1 + TwoCoin.failure 1 1 1 = 0 := by
  norm_num [TwoCoin.success, TwoCoin.failure]
example (p q r : unitInterval) :
    RealCoin.credit (TwoCoin.bias p q r 0) (fun b => if b then ∞ else 0) = 0 := by
  have h : TwoCoin.bias p q r 0 = 0 := by
    apply Subtype.ext
    rw [TwoCoin.bias_coe]
    simp
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]
example : (TwoCoin.weightBias 0 3 (by decide) : ℝ) = 0 := by
  norm_num [TwoCoin.weightBias, RationalCoin.bias]
example : (TwoCoin.weightBias 3 0 (by decide) : ℝ) = 1 := by
  norm_num [TwoCoin.weightBias, RationalCoin.bias]
example : (TwoCoin.portkeyBias 0 3 (by decide) (by decide) : ℝ) = 0 := by
  norm_num [TwoCoin.portkeyBias, RationalCoin.bias]

example (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ n, ENNReal.ofReal (q ^ n) ∂ProbabilityTheory.poissonMeasure 0) = 1 := by
  simpa using Distributions.lintegral_poisson_pow 0 q hq

example (r : ℝ≥0) :
    (∫⁻ n, ENNReal.ofReal ((1:ℝ) ^ n) ∂ProbabilityTheory.poissonMeasure r) = 1 := by
  simp

example (r : ℝ≥0) :
    (∫⁻ n, ENNReal.ofReal ((0:ℝ) ^ n) ∂ProbabilityTheory.poissonMeasure r) =
      ENNReal.ofReal (Real.exp (-(r:ℝ))) := by
  simpa using Distributions.lintegral_poisson_pow r 0 (by norm_num)

example (r : ℝ≥0) :
    (∫⁻ n, ENNReal.ofReal ((2:ℝ) ^ n) ∂ProbabilityTheory.poissonMeasure r) =
      ENNReal.ofReal (Real.exp (r:ℝ)) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using
    Distributions.lintegral_poisson_pow r 2 (by norm_num)

example (x y : ℕ) : ExpMinusScaled.bias 0 x y = 1 := by
  apply Subtype.ext
  simp [ExpMinusScaled.bias]
example (p : unitInterval) (y : ℕ) : ExpMinusScaled.bias p 0 y = 1 := by
  apply Subtype.ext
  simp [ExpMinusScaled.bias]
example (x y : ℕ) (hy : 0 < y) :
    ExpMinusScaled.bias 1 x y =
      ExpMinusRational.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy) := by
  apply Subtype.ext
  simp [ExpMinusScaled.bias, ExpMinusRational.bias]
example (p : unitInterval) (y : ℕ) :
    RealCoin.credit (ExpMinusScaled.bias p 0 y) (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpMinusScaled.bias]

example (a b : ℕ) : TanhScaled.bias 0 a b = 0 := by
  apply Subtype.ext
  simp [TanhScaled.coe_bias]
example (p : unitInterval) (b : ℕ) : TanhScaled.bias p 0 b = 0 := by
  apply Subtype.ext
  simp [TanhScaled.coe_bias]
example (a b : ℕ) :
    RealCoin.credit (TanhScaled.bias 0 a b) (fun b => if b then ∞ else 0) = 0 := by
  have h : TanhScaled.bias 0 a b = 0 := by
    apply Subtype.ext
    simp [TanhScaled.coe_bias]
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]

example (a : ℤ) (b : ℕ) : (SigmoidScaled.bias 0 a b : ℝ) = 1/2 := by
  norm_num [SigmoidScaled.bias]
example (p : unitInterval) (b : ℕ) : (SigmoidScaled.bias p 0 b : ℝ) = 1/2 := by
  norm_num [SigmoidScaled.bias]
example (p : unitInterval) : (SigmoidScaled.bias p (-2) 3 : ℝ) =
    1/(1+Real.exp ((2:ℝ)/3*(p:ℝ))) := by
  norm_num [SigmoidScaled.bias]
example (p : unitInterval) : (SigmoidScaled.bias p 2 3 : ℝ) =
    1/(1+Real.exp ((-2:ℝ)/3*(p:ℝ))) := by rfl

#print axioms SampLib.TwoCoin.twoCoin_distSpec
#print axioms SampLib.TwoCoin.expectation
#print axioms SampLib.TwoCoin.bias_coe
#print axioms SampLib.ExponentialTwist.exponentialTwist_distSpec
#print axioms SampLib.ExponentialTwist.expectation
#print axioms SampLib.ExponentialTwist.coe_bias
#print axioms SampLib.Distributions.lintegral_poisson_pow
#print axioms SampLib.ExpMinusScaled.expMinusScaled_distSpec
#print axioms SampLib.ExpMinusScaled.law_eq
#print axioms SampLib.ExpMinusScaled.expectation
#print axioms SampLib.TanhScaled.tanhScaled_distSpec
#print axioms SampLib.TanhScaled.coe_bias
#print axioms SampLib.SigmoidScaled.sigmoidScaled_distSpec

end
end ExpansionFactoriesReview
