import SampLib.Bernoulli.LowProbabilityRepair

open ProbLang
open scoped ENNReal

namespace ExactFactoriesRepairReview

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

example (E : CoPset) (p : unitInterval) (σ : LowProbabilityRepair.Parameters p)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LowProbabilityRepair.lowProbabilityRepair_distSpec E p σ coin hcoin) F I

private def defectBoundary : LowProbabilityRepair.Parameters LowProbabilityMargin.counterexampleBias :=
  ⟨2, 1, 1, 4, LowProbabilityMargin.counterexample_admissible⟩

private def zeroBoundary : LowProbabilityRepair.Parameters 0 :=
  ⟨2, 1, 0, 1, by norm_num [LowProbabilityMargin.Admissible, Gambler.ratio]⟩

private def contractingBoundary : LowProbabilityRepair.Parameters
    (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) :=
  ⟨1, 2, 1, 4, by norm_num [LowProbabilityMargin.Admissible, Gambler.ratio]⟩

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #())
      (RealCoin.law LowProbabilityMargin.counterexampleBias) Val.bool)
    (I : IProp GF) :=
  frame (LowProbabilityRepair.lowProbabilityRepair_distSpec E _ defectBoundary coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (LowProbabilityRepair.lowProbabilityRepair_distSpec E 0 zeroBoundary coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #())
      (RealCoin.law (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) Val.bool)
    (I : IProp GF) :=
  frame (LowProbabilityRepair.lowProbabilityRepair_distSpec E _ contractingBoundary coin hcoin)
    (fun b => if b then 0 else ∞) I

example : (defectBoundary.bias : ℝ) = 1 / 4 := by
  norm_num [LowProbabilityRepair.Parameters.bias_coe, defectBoundary,
    LowProbabilityMargin.counterexampleBias, Gambler.ratio]

example : (zeroBoundary.bias : ℝ) = 0 := by
  norm_num [LowProbabilityRepair.Parameters.bias_coe, zeroBoundary, Gambler.ratio]

example : (contractingBoundary.bias : ℝ) = 1 / 4 := by
  norm_num [LowProbabilityRepair.Parameters.bias_coe, contractingBoundary, Gambler.ratio]

#print axioms LowProbabilityRepair.lowProbabilityRepair_distSpec
#print axioms LowProbabilityRepair.twp_lowProbabilityRepair
#print axioms LowProbabilityRepair.expectation
#print axioms LowProbabilityMargin.counterexample_inner_not_admissible
#print axioms LowProbabilityMargin.repaired_inner_admissible

end

end ExactFactoriesRepairReview
