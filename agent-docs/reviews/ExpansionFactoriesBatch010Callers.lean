import SampLib.Bernoulli.AffineRatio
import SampLib.Bernoulli.LinearPower
import SampLib.Bernoulli.Addition
import SampLib.Bernoulli.Subtraction
import SampLib.Bernoulli.Division
import SampLib.Bernoulli.AffineFactory
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

example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearPower.linearPower_zero_distSpec (GF := GF) E coin (-9) 0 (-3) 0) F I

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearPower.linearPower_distSpec E p a b e f h coin hc n) F I

example (E : CoPset) (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (p : ℝ)+q ≤ 1-(e : ℝ)/f) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (Addition.addition_distSpec E p q e f he hef h left right hl hr) F I

example (E : CoPset) (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ)/f ≤ (p : ℝ)-q) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (Subtraction.subtraction_distSpec E p q e f he hef h left right hl hr) F I

example (E : CoPset) (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ)/f ≤ (p : ℝ)-q) (den num : Val rT)
    (hd : IsDistSpec (GF := GF) E pl(&den.fst #()) (RealCoin.law p) Val.bool)
    (hn : IsDistSpec (GF := GF) E pl(&num.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (Division.division_distSpec E p q e f he hef h den num hd hn) F I

example (E : CoPset) (p : unitInterval) (a b x y e f : ℤ)
    (h : AffineFactory.Admissible p a b x y e f) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AffineFactory.affine_distSpec E p a b x y e f h coin hc) F I

private def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
private def quarter : unitInterval := ⟨1/4, by norm_num, by norm_num⟩
example : (Addition.bias quarter quarter 1 2 (by norm_num) (by norm_num)
    (by norm_num [quarter]) : ℝ) = 1/2 := by rw [Addition.bias_coe]; norm_num [quarter]
example : (Subtraction.bias 1 half 1 2 (by norm_num) (by norm_num)
    (by norm_num [half]) : ℝ) = 1/2 := by rw [Subtraction.bias_coe]; norm_num [half]
example : (Division.bias half quarter 1 4 (by norm_num) (by norm_num)
    (by norm_num [half,quarter]) : ℝ) = 1/2 := by
  rw [Division.bias_coe]; norm_num [half,quarter]
example : (Division.bias 1 0 1 2 (by norm_num) (by norm_num)
    (by norm_num) : ℝ) = 0 := by rw [Division.bias_coe]; norm_num
example (h : AffineFactory.Admissible quarter 1 2 0 1 1 2) :
    (AffineFactory.bias quarter 1 2 0 1 1 2 h : ℝ) = 1/2 := by
  exact (AffineFactory.bias_coe _ _ _ _ _ _ _ h).trans (by norm_num [quarter])
example : AffineFactory.Admissible quarter 1 2 0 1 1 2 := by
  norm_num [AffineFactory.Admissible, quarter]
example (h : AffineFactory.Admissible 0 2 1 1 1 (-17) 0) :
    (AffineFactory.bias 0 2 1 1 1 (-17) 0 h : ℝ) = 1/2 := by
  exact (AffineFactory.bias_coe _ _ _ _ _ _ _ h).trans (by norm_num)
example : AffineFactory.Admissible 0 2 1 1 1 (-17) 0 := by
  norm_num [AffineFactory.Admissible]

example (h : ((1 : ℤ) : ℝ)/((2 : ℤ) : ℝ) ≤
    ((1 : unitInterval) : ℝ)-((0 : unitInterval) : ℝ)) :
    (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
      ∂RealCoin.law (Division.bias 1 0 1 2 (by norm_num) (by norm_num) h)) = 0 := by
  have hb : Division.bias 1 0 1 2 (by norm_num) (by norm_num) h = 0 :=
    Subtype.ext ((Division.bias_coe _ _ _ _ _ _ h).trans (by norm_num))
  rw [hb]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (coin : Val rT) (I : IProp GF) :=
  frame (LinearPower.linearPower_zero_distSpec (GF := GF) E coin 0 0 (-8) 0)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (p q : unitInterval) (a b x y : ℕ) (e f : ℤ)
    (hb : 0 < b) (hy : 0 < y)
    (h : AffineRatio.Admissible p q (a*y) (x*b) (b*y) e f) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AffineRatio.affineRatio_distSpec E p q a b x y e f hb hy h left right hl hr) F I

example : AffineRatio.Admissible 0 1 1 0 1 (-17) 0 := Or.inl (by norm_num)
example (h : AffineRatio.Admissible 0 1 1 0 1 (-17) 0) :
    (AffineRatio.bias 0 1 1 0 1 (-17) 0 (by norm_num) h : ℝ) = 1 := by
  norm_num [AffineRatio.bias, AffineRatio.numerator, AffineRatio.denominator]
example : AffineRatio.Admissible half quarter 0 0 1 1 4 := by
  right
  norm_num [AffineRatio.numerator, AffineRatio.denominator, half, quarter]
example (h : AffineRatio.Admissible half quarter 0 0 1 1 4) :
    (AffineRatio.bias half quarter 0 0 1 1 4 (by norm_num) h : ℝ) = 1/2 := by
  norm_num [AffineRatio.bias, AffineRatio.numerator, AffineRatio.denominator, half, quarter]
example : AffineRatio.Admissible 1 0 0 0 1 1 2 := by
  right
  norm_num [AffineRatio.numerator, AffineRatio.denominator]
example (h : AffineRatio.Admissible 1 0 0 0 1 1 2) :
    (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
      ∂RealCoin.law (AffineRatio.bias 1 0 0 0 1 1 2 (by norm_num) h)) = 0 := by
  have hb : AffineRatio.bias 1 0 0 0 1 1 2 (by norm_num) h = 0 := by
    apply Subtype.ext
    norm_num [AffineRatio.bias, AffineRatio.numerator, AffineRatio.denominator]
  rw [hb]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

#print axioms SampLib.AffineRatio.affineRatio_distSpec
#print axioms SampLib.AffineRatio.direct_expectation
#print axioms SampLib.AffineRankCoin.distSpec

#print axioms SampLib.LinearPower.linearPower_zero_distSpec
#print axioms SampLib.LinearPower.linearPower_distSpec
#print axioms SampLib.Addition.addition_distSpec
#print axioms SampLib.Subtraction.subtraction_distSpec
#print axioms SampLib.Subtraction.expectation
#print axioms SampLib.Division.division_distSpec
#print axioms SampLib.AffineFactory.affine_distSpec
end
end ExpansionFactoriesReview
