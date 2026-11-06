import SampLib.Weighted.UniformBinaryFloat
import SampLib.Discrete.WalleniusMultivariate
import SampLib.Discrete.MultivariateHypergeometric
import SampLib.Weighted.VoseSamples

open ProbLang
open scoped ENNReal

namespace ReviewExpansionStructured

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A caller retains its own resource while spending the expected sampler credit. -/
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

local instance : NeZero ([0, 1, 1] : List ℕ).sum := ⟨by decide⟩

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (precision cap : ℕ) (F : ℤ × ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (UniformBinaryFloat.uniformBinaryFloat_distSpec E precision cap)
    F (measurable_of_countable _) R

example (E : CoPset) (n : ℕ) (pop odds : List ℕ) (hn : n ≤ pop.sum)
    (hl : pop.length = odds.length) (ho : ∀ o ∈ odds, 0 < o)
    (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (WalleniusMultivariate.walleniusMultivariate_distSpec E n pop odds hn hl ho)
    F (measurable_of_countable _) R

example (E : CoPset) (n : ℕ) (pop : List ℕ) (hn : n ≤ pop.sum)
    (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (MultivariateHypergeometric.multivariateHypergeometric_distSpec E n pop hn)
    F (measurable_of_countable _) R

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (n : ℕ)
    (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (VoseSamples.voseSamples_distSpec E ws n) F (measurable_of_countable _) R

example (E : CoPset) (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (VoseSamples.voseSamples_distSpec E [0, 1, 1] 2)
    F (measurable_of_countable _) R

example (E : CoPset) (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (WalleniusMultivariate.walleniusMultivariate_distSpec E 2 [1, 0, 1] [1, 17, 3]
    (by decide) rfl (by simp)) F (measurable_of_countable _) R

example (E : CoPset) :=
  WalleniusMultivariate.walleniusMultivariate_distSpec (rT := rT) (GF := GF) E
    0 [] [] (by decide) rfl (by simp)

end integer_draws

open MeasureTheory
open scoped Classical

example (precision : ℕ) : UniformBinaryFloat.law precision 0 = Measure.dirac (0, 0) := by simp

example (precision cap : ℕ) :
    (∫⁻ _, (∞ : ℝ≥0∞) ∂UniformBinaryFloat.law precision cap) = ∞ := by simp

example : (∫⁻ x, (if x = (1, -2) then 1 else 0 : ℝ≥0∞)
    ∂UniformBinaryFloat.law 0 2) = 1 / 4 := by
  change UniformBinaryFloat.credit 0 2 0 _ = _
  rw [← UniformBinaryFloat.expectation 0 1 0, RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, UniformBinaryFloat.coinCredit]
  rw [← UniformBinaryFloat.expectation 0 0 1, RealCoin.lintegral_law]
  norm_num [RealCoin.credit, RealCoin.pmf, UniformBinaryFloat.coinCredit,
    UniformBinaryFloat.point, UniformInt.lintegral_law, Finset.sum_range_succ,
    VonNeumann.fairBias]
  simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

example : Wallenius.wordLaw [1, 0, 1] [1, 17, 3] 2 {[0, 2]} = 1 / 4 := by
  have h := Wallenius.word_likelihood [1, 0, 1] [1, 17, 3] [0, 2]
  norm_num only [List.length_cons, List.length_nil] at h
  rw [h]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]
  rw [ENNReal.div_self (by norm_num) (by norm_num), mul_one]

example : Wallenius.wordLaw [1, 0, 1] [1, 17, 3] 2 {[2, 0]} = 3 / 4 := by
  have h := Wallenius.word_likelihood [1, 0, 1] [1, 17, 3] [2, 0]
  norm_num only [List.length_cons, List.length_nil] at h
  rw [h]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]

example : Wallenius.wordLaw [1, 0, 1] [1, 1, 1] 2 {[0, 2]} = 1 / 2 := by
  have h := Wallenius.word_likelihood [1, 0, 1] [1, 1, 1] [0, 2]
  norm_num only [List.length_cons, List.length_nil] at h
  rw [h]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]

example : Wallenius.colorCounts 3 [2, 0] = [1, 0, 1] := by decide
example : Wallenius.law 0 [] [] = Measure.dirac [] := by simp

example (n : ℕ) (pop odds : List ℕ) :
    (∫⁻ _, (∞ : ℝ≥0∞) ∂Wallenius.law n pop odds) = ∞ := by simp

example : VoseSamples.law [0, 1, 1] 0 = Measure.dirac [] := by simp
example (n : ℕ) : (∫⁻ _, (∞ : ℝ≥0∞) ∂VoseSamples.law [0, 1, 1] n) = ∞ := by simp

example : (∫⁻ xs, (if xs = [1, 2] then 1 else 0 : ℝ≥0∞)
    ∂VoseSamples.law [0, 1, 1] 2) = 1 / 4 := by
  rw [← VoseSamples.expectation _ _ _ (measurable_of_countable _)]
  simp_rw [SampleWithReplacement.lintegral_law_succ _ _ _ (measurable_of_countable _)]
  simp only [SampleWithReplacement.law, lintegral_dirac]
  simp_rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, List.ofFn_succ]
  rw [div_eq_mul_inv, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

example : (∫⁻ xs, (if xs = [0, 0] then ∞ else 0 : ℝ≥0∞)
    ∂VoseSamples.law [0, 1, 1] 2) = 0 := by
  rw [← VoseSamples.expectation _ _ _ (measurable_of_countable _)]
  simp_rw [SampleWithReplacement.lintegral_law_succ _ _ _ (measurable_of_countable _)]
  simp only [SampleWithReplacement.law, lintegral_dirac]
  simp_rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, List.ofFn_succ]

#print axioms SampLib.UniformBinaryFloat.uniformBinaryFloat_distSpec
#print axioms SampLib.UniformBinaryFloat.expectation
#print axioms SampLib.WalleniusMultivariate.walleniusMultivariate_distSpec
#print axioms SampLib.MultivariateHypergeometric.multivariateHypergeometric_distSpec
#print axioms SampLib.NatUrnOps.twp_validUrn
#print axioms SampLib.NatUrnOps.twp_urnWeights
#print axioms SampLib.VoseSamples.voseSamples_distSpec
#print axioms SampLib.VoseTable.twp_voseTable
#print axioms SampLib.VoseBalance.finishedTable_mass

end
end ReviewExpansionStructured
