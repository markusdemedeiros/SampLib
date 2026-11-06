import SampLib.Samplers.ReciprocalAffine
import SampLib.Samplers.ReciprocalAffinePower
import SampLib.Samplers.InverseQuadratic
import SampLib.Samplers.SqrtTwoMinusOne
import SampLib.Samplers.InverseSqrtTwo
import SampLib.Samplers.GoldenFamily
import SampLib.Samplers.OffsetRace
import SampLib.Samplers.LogOverAffine
import SampLib.Templates
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

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (p : unitInterval) (a b x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hd : x*b ≤ a*y) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalAffine.reciprocalAffine_distSpec E p a b x y ha hb hy hd coin hc) F I

example (E : CoPset) (p : unitInterval) (a b x y k : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hd : x*b ≤ a*y) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalAffinePower.reciprocalAffinePower_distSpec E p coin a b x y k
    ha hb hy hd hc) F I

example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalAffinePower.reciprocalAffinePower_zero_distSpec E coin (-7) 0 (-9) 0) F I

example (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseQuadratic.inverseQuadratic_distSpec E p m coin hc) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (SqrtTwoMinusOne.sqrtTwoMinusOne_distSpec (rT := rT) (GF := GF) E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseSqrtTwo.inverseSqrtTwo_distSpec (rT := rT) (GF := GF) E) F I

example (E : CoPset) (a : GoldenFamily.Parameters) (k : ℕ)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (GoldenFamily.goldenFamily_distSpec (rT := rT) (GF := GF) E a k) F I

example (E : CoPset) (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ)/b + (p : ℝ) + (x : ℝ)/y + (q : ℝ)) (pc qc : Val rT)
    (hp : IsDistSpec (GF := GF) E pl(&pc.fst #()) (RealCoin.law p) Val.bool)
    (hq : IsDistSpec (GF := GF) E pl(&qc.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (OffsetRace.offsetRace_distSpec E p q a b x y hb hy h pc qc hp hq) F I

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (coin : Val rT) (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogOverAffine.logOverAffine_distSpec E p a b hb hab coin hc) F I

example (p : unitInterval) :
    (ReciprocalAffine.bias p 3 0 5 (by decide) (by decide) : ℝ) = 0 := by
  simp [ReciprocalAffine.bias]

example : (ReciprocalAffine.bias 0 3 3 5 (by decide) (by decide) : ℝ) = 1 := by
  norm_num [ReciprocalAffine.bias]

example : (ReciprocalAffine.bias 1 3 3 5 (by decide) (by decide) : ℝ) = 3/8 := by
  norm_num [ReciprocalAffine.bias]

example (p : unitInterval) :
    RealCoin.credit (ReciprocalAffine.bias p 3 0 5 (by decide) (by decide))
      (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ReciprocalAffine.bias]

example (p : unitInterval) :
    IterateCoin.credit (ReciprocalAffine.bias p 3 0 5 (by decide) (by decide)) 0
      (fun b => if b then 0 else ∞) = 0 := by simp

example : (InverseQuadratic.bias 0 0 : ℝ) = 1 := by norm_num [InverseQuadratic.bias]
example : (InverseQuadratic.bias 1 0 : ℝ) = 1/2 := by norm_num [InverseQuadratic.bias]
example : (InverseQuadratic.bias 0 2 : ℝ) = 1/5 := by norm_num [InverseQuadratic.bias]

example : RealCoin.credit (InverseQuadratic.bias 0 0) (fun b => if b then 0 else ∞) = 0 := by
  norm_num [RealCoin.credit, RealCoin.pmf, InverseQuadratic.bias]

example : (SqrtTwoMinusOne.bias : ℝ) = Real.sqrt 2 - 1 := rfl
example : (InverseSqrtTwo.bias : ℝ) = 1 / Real.sqrt 2 := by
  simp [InverseSqrtTwo.bias, AlgebraicConstants.inverseSqrtTwoBias, one_div]
example : ((1:ℤ)*1 + 2*1*3 - 3*3).sign = -1 := by decide
example : (2*(3:ℤ)*3 - 4*4).sign = 1 := by decide

private def goldenPlus : GoldenFamily.Parameters := ⟨1,1,by decide,Or.inl rfl,by simp⟩
private def goldenMinus : GoldenFamily.Parameters := ⟨3,-1,by decide,Or.inr rfl,by simp⟩
example : (GoldenFamily.bias goldenPlus : ℝ) = Real.goldenRatio⁻¹ := by
  norm_num [GoldenFamily.bias, GoldenFamily.shape, goldenPlus, Real.goldenRatio]
example : (GoldenFamily.bias goldenMinus : ℝ) = ((3 + Real.sqrt 5)/2)⁻¹ := by
  norm_num [GoldenFamily.bias, GoldenFamily.shape, goldenMinus]
example (a : GoldenFamily.Parameters) :
    IterateCoin.credit (GoldenFamily.bias a) 0 (fun b => if b then 0 else ∞) = 0 := by simp
example (a : GoldenFamily.Parameters) (k : ℕ) :
    (IterateCoin.bias (GoldenFamily.bias a) k : ℝ) = GoldenFamily.shape a ^ (-(k : ℤ)) :=
  GoldenFamily.bias_power a k

example : (OffsetRace.bias 0 1 0 1 0 1 (by decide) (by decide) : ℝ) = 1 := by
  norm_num [OffsetRace.bias_coe]
example : (OffsetRace.bias 1 0 0 1 0 1 (by decide) (by decide) : ℝ) = 0 := by
  norm_num [OffsetRace.bias_coe]
example : (OffsetRace.bias 1 1 0 1 0 1 (by decide) (by decide) : ℝ) = 1/2 := by
  norm_num [OffsetRace.bias_coe]
example : (OffsetRace.bias 0 0 2 3 5 7 (by decide) (by decide) : ℝ) = 15/29 := by
  norm_num [OffsetRace.bias_coe]

example : (LogOverAffine.bias 0 1 1 (by decide) (by decide) : ℝ) = 0 := by
  rw [LogOverAffine.bias_coe]
  norm_num
example : RealCoin.credit (LogOverAffine.bias 0 1 1 (by decide) (by decide))
    (fun b => if b then ∞ else 0) = 0 := by
  have h : LogOverAffine.bias 0 1 1 (by decide) (by decide) = 0 := by
    apply Subtype.ext
    rw [LogOverAffine.bias_coe]
    norm_num
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]

-- Both context stepping and recursive beta stepping use the checked rule.
example (E : CoPset) (Φ : Val rT → IProp GF) :
    tglWp E pl(#3 + #4) Φ ⊢ tglWp E pl(((fun x, x) #3) + #4) Φ := by
  iintro H
  twp_step
  simp [Exp.open', Exp.openRec, Exp.closeRec, Exp.ofVal]
  iexact H

example (E : CoPset) (Φ : Val rT → IProp GF) :
    tglWp E pl(#3) Φ ⊢ tglWp E pl((rec f x := x) #3) Φ := by
  iintro H
  twp_step
  simp [Exp.open', Exp.openRec, Exp.closeRec]
  twp_step
  simp [Exp.open', Exp.openRec]
  iexact H

#print axioms SampLib.ReciprocalAffine.reciprocalAffine_distSpec
#print axioms SampLib.ReciprocalAffinePower.reciprocalAffinePower_distSpec
#print axioms SampLib.InverseQuadratic.inverseQuadratic_distSpec
#print axioms SampLib.SqrtTwoMinusOne.sqrtTwoMinusOne_distSpec
#print axioms SampLib.InverseSqrtTwo.inverseSqrtTwo_distSpec
#print axioms SampLib.GoldenFamily.goldenFamily_distSpec
#print axioms SampLib.OffsetRace.offsetRace_distSpec
#print axioms SampLib.LogOverAffine.logOverAffine_distSpec
#print axioms SampLib.ReciprocalAffine.expectation
#print axioms SampLib.ReciprocalAffinePower.reciprocalAffinePower_zero_distSpec
#print axioms SampLib.InverseQuadratic.reciprocal_bias
#print axioms SampLib.GoldenFamily.polynomial_sign
#print axioms SampLib.GoldenFamily.bias_equation
#print axioms SampLib.OffsetRace.expectation
#print axioms SampLib.OffsetRace.bias_coe
#print axioms SampLib.LogOverAffine.bias_coe

end
end ExpansionFactoriesReview
