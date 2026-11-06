import SampLib.Samplers.PiConstants
import SampLib.Samplers.CoinProduct

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview001

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
  frame (PiConstants.piQuarter_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.piTwelfth_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.piQuarterMinusHalf_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.piMinusThreeOverFour_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.piMinusThree_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.inversePi_distSpec E) F I

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiConstants.fourOverThreePi_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (PiConstants.piQuarter_distSpec E) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (PiConstants.inversePi_distSpec E) (fun b => if b then 0 else ∞) I

example : (PiConstants.quarterBias : ℝ) = Real.pi / 4 :=
  PiConstants.quarterBias_coe

example : (PiConstants.twelfthBias : ℝ) = Real.pi / 12 :=
  PiConstants.twelfthBias_coe

example : (PiConstants.quarterMinusHalfBias : ℝ) = Real.pi / 4 - 1 / 2 :=
  PiConstants.quarterMinusHalfBias_coe

example : (PiConstants.minusThreeOverFourBias : ℝ) = (Real.pi - 3) / 4 :=
  PiConstants.minusThreeOverFourBias_coe

example : (PiConstants.minusThreeBias : ℝ) = Real.pi - 3 :=
  PiConstants.minusThreeBias_coe

example : (PiConstants.inverseBias : ℝ) = 1 / Real.pi :=
  PiConstants.inverseBias_coe

example : (PiConstants.fourOverThreeBias : ℝ) = 4 / (3 * Real.pi) :=
  PiConstants.fourOverThreeBias_coe

#print axioms PiConstants.piQuarter_distSpec
#print axioms PiConstants.piTwelfth_distSpec
#print axioms PiConstants.piQuarterMinusHalf_distSpec
#print axioms PiConstants.piMinusThreeOverFour_distSpec
#print axioms PiConstants.piMinusThree_distSpec
#print axioms PiConstants.inversePi_distSpec
#print axioms PiConstants.fourOverThreePi_distSpec

end

end ExactFactoriesReview001
