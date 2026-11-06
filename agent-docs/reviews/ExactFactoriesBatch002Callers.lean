import SampLib.Samplers.LogOnePlusRational
import SampLib.Samplers.RationalIntegerPower

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview002

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

example (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogOnePlusRational.logOnePlusRational_distSpec E a b ha hb hab) F I

example (E : CoPset) (I : IProp GF) :=
  frame (LogOnePlusRational.logOnePlusRational_distSpec E 0 7
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (LogOnePlusRational.logOnePlusRational_distSpec E 7 7
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then 0 else ∞) I

example (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (n : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (RationalIntegerPower.rationalIntegerPower_distSpec E a b ha hb hab n) F I

example (E : CoPset) (I : IProp GF) :=
  frame (RationalIntegerPower.rationalIntegerPower_distSpec E 0 7
    (by norm_num) (by norm_num) (by norm_num) 0) (fun b => if b then 0 else ∞) I

example (E : CoPset) (n : ℕ) (I : IProp GF) :=
  frame (RationalIntegerPower.rationalIntegerPower_distSpec E 0 7
    (by norm_num) (by norm_num) (by norm_num) (n + 1)) (fun b => if b then ∞ else 0) I

example (E : CoPset) (n : ℕ) (I : IProp GF) :=
  frame (RationalIntegerPower.rationalIntegerPower_distSpec E 7 7
    (by norm_num) (by norm_num) (by norm_num) n) (fun b => if b then 0 else ∞) I

example : (LogOnePlusRational.bias 0 7 (by norm_num) (by norm_num) (by norm_num) : ℝ) = 0 := by
  simp

example :
    (RationalIntegerPower.bias 0 7 (by norm_num) (by norm_num) (by norm_num) 0 : ℝ) = 1 := by
  simp

example (n : ℕ) :
    (RationalIntegerPower.bias 0 7 (by norm_num) (by norm_num) (by norm_num) (n + 1) : ℝ) = 0 := by
  simp

example (n : ℕ) :
    (RationalIntegerPower.bias 7 7 (by norm_num) (by norm_num) (by norm_num) n : ℝ) = 1 := by
  simp

#print axioms LogOnePlusRational.logOnePlusRational_distSpec
#print axioms RationalIntegerPower.rationalIntegerPower_distSpec

end

end ExactFactoriesReview002
