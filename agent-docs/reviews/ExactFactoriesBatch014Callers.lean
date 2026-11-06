import SampLib.Samplers.EContinuedFractionConstants

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview014

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

example (E : CoPset) (a b j : ℕ) (hb : 0 < b) (hab : b ≤ a) (hj : 0 < j)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EContinuedFraction.eContinuedFraction_distSpec E a b j hb hab hj) F I

example (E : CoPset) (I : IProp GF) :=
  frame (EContinuedFraction.eContinuedFraction_distSpec E 1 1 1
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (EContinuedFraction.eContinuedFraction_distSpec E 3 2 6
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then 0 else ∞) I

example (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EContinuedFractionConstants.inverseEPlusContinuedFraction_distSpec E a b hb hab) F I

example (E : CoPset) (I : IProp GF) :=
  frame (EContinuedFractionConstants.inverseEPlusContinuedFraction_distSpec E 1 1
    (by norm_num) (by norm_num)) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (EContinuedFractionConstants.inverseEPlusContinuedFraction_distSpec E 3 2
    (by norm_num) (by norm_num)) (fun b => if b then 0 else ∞) I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EContinuedFractionConstants.eMinusTwoContinuedFraction_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (EContinuedFractionConstants.eMinusTwoContinuedFraction_distSpec E)
    (fun b => if b then ∞ else 0) I

example : (EContinuedFraction.bias 1 1 (by norm_num) (by norm_num) 1 : ℝ) =
    1 / (Real.exp 1 - 1) := by
  rw [EContinuedFractionConstants.bias_one]
  simp only [Nat.cast_one, div_one]
  congr 1
  ring

example (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (EContinuedFraction.bias a b hb hab 2 : ℝ) = Real.exp 1 - 2 :=
  EContinuedFractionConstants.bias_two a b hb hab

example : EContinuedFraction.denominator 10 3 = 2 := by
  norm_num [EContinuedFraction.denominator]

example : EContinuedFraction.denominator 10 6 = 4 := by
  norm_num [EContinuedFraction.denominator]

example : EContinuedFraction.denominator 10 4 = 1 := by
  norm_num [EContinuedFraction.denominator]

example : EContinuedFraction.scale 7 1 = 7 := by norm_num [EContinuedFraction.scale]

example : EContinuedFraction.scale 7 2 = 1 := by norm_num [EContinuedFraction.scale]

#print axioms EContinuedFraction.eContinuedFraction_distSpec
#print axioms EContinuedFraction.twp_eContinuedFraction
#print axioms EContinuedFractionConstants.inverseEPlusContinuedFraction_distSpec
#print axioms EContinuedFractionConstants.eMinusTwoContinuedFraction_distSpec
#print axioms EContinuedFractionConstants.bias_one
#print axioms EContinuedFractionConstants.bias_two
#print axioms EulerContinuedFraction.value_one
#print axioms EulerContinuedFraction.value_two

end

end ExactFactoriesReview014
