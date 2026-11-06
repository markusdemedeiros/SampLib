import SampLib.Constants.EulerScaledConstants
import SampLib.Constants.InverseEPlus
import SampLib.Constants.EulerAffineConstants

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview003

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
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

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EulerScaledConstants.eDivThree_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EulerScaledConstants.eQuarter_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (EulerScaledConstants.eDivThree_distSpec E) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (EulerScaledConstants.eQuarter_distSpec E) (fun b => if b then 0 else ∞) I

example : (EulerScaledConstants.third : ℝ) = Real.exp 1 / 3 := by
  simp [EulerScaledConstants.third, EScaled.bias]

example : (EulerScaledConstants.quarter : ℝ) = Real.exp 1 / 4 := by
  simp [EulerScaledConstants.quarter, EScaled.bias]

example : RealCoin.credit EulerScaledConstants.third (fun _ => ∞) = ∞ := by
  rw [← RealCoin.lintegral_law]
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

example : RealCoin.credit EulerScaledConstants.quarter (fun _ => ∞) = ∞ := by
  rw [← RealCoin.lintegral_law]
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

example (E : CoPset) (c : ℕ) (hc : 1 ≤ c) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseEPlus.inverseEPlus_distSpec E c hc) F I

example (E : CoPset) (I : IProp GF) :=
  frame (InverseEPlus.inverseEPlus_distSpec E 1 (by norm_num))
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (InverseEPlus.inverseEPlus_distSpec E 2 (by norm_num))
    (fun b => if b then 0 else ∞) I

example (c : ℕ) (hc : 1 ≤ c) :
    (InverseEPlus.bias c hc : ℝ) = 1 / (Real.exp 1 + c - 2) := by
  simp [InverseEPlus.bias, InverseEPlusRational.bias, EulerReciprocal.center]

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EulerAffineConstants.eMinusTwo_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EulerAffineConstants.threeMinusE_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (EulerAffineConstants.eMinusTwo_distSpec E) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (EulerAffineConstants.threeMinusE_distSpec E) (fun b => if b then 0 else ∞) I

example : (EulerConstants.minusTwo : ℝ) = Real.exp 1 - 2 := rfl

example : (EulerConstants.threeMinus : ℝ) = 3 - Real.exp 1 := rfl

example : FromBounds.encodeInterval (rT := rT) (EulerConstants.minusTwoInterval 0) =
    Val.pair (Val.int 0) (Val.pair (Val.int 1) (Val.int 1)) := rfl

example : FromBounds.encodeInterval (rT := rT) (EulerConstants.threeMinusInterval 0) =
    Val.pair (Val.int 0) (Val.pair (Val.int 1) (Val.int 1)) := rfl

#print axioms EulerAffineConstants.eMinusTwo_distSpec
#print axioms EulerAffineConstants.threeMinusE_distSpec
#print axioms InverseEPlus.inverseEPlus_distSpec
#print axioms EulerScaledConstants.eDivThree_distSpec
#print axioms EulerScaledConstants.eQuarter_distSpec

end

end ExactFactoriesReview003
