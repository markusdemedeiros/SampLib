import SampLib.Constants.ErfRatio
import SampLib.Constants.LowerGammaIntegerRatio

open ProbLang
open scoped ENNReal

namespace SpecialIntegralCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

omit [ProbLangDist.IsUniformReal ℝ] in
theorem framed {E : CoPset} {e : Exp ℝ} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (x : unitInterval) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  framed (ErfRatio.erfRatio_distSpec E x) F I

example (E : CoPset) (I : IProp GF) :=
  framed (ErfRatio.erfRatio_distSpec E 0) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  framed (ErfRatio.erfRatio_distSpec E 1) (fun b => if b then 0 else ∞) I

example (x : unitInterval) :
    (ErfRatio.bias x : ℝ) = ErrorFunctionKernel.erf x / ErrorFunctionKernel.erf 1 :=
  ErfRatio.bias_coe x x.2

example (E : CoPset) (m : ℕ) (hm : 0 < m) (x : unitInterval)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  framed (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E m hm x) F I

example (E : CoPset) (I : IProp GF) :=
  framed (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E 1 (by decide) 0)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (m : ℕ) (hm : 0 < m) (I : IProp GF) :=
  framed (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E m hm 1)
    (fun b => if b then 0 else ∞) I

example (n : ℕ) (x : unitInterval) :
    (LowerGammaIntegerRatio.bias n x : ℝ) =
      IntegerGammaKernel.lowerGamma n x / IntegerGammaKernel.lowerGamma n 1 :=
  LowerGammaIntegerRatio.bias_coe n x x.2

#print axioms ErfRatio.erfRatio_distSpec
#print axioms ErfRatio.bias_coe
#print axioms LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec
#print axioms LowerGammaIntegerRatio.twp_lowerGammaIntegerRatio
#print axioms LowerGammaIntegerRatio.bias_coe
#print axioms SquaredDecreasingChain.twp_chain
#print axioms SquaredDecreasingChain.expectation
#print axioms OrderStatisticMaximum.orderStatistic_max_distSpec

end

end SpecialIntegralCallers
