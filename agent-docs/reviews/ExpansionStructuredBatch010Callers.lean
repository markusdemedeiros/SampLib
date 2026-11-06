import SampLib.General.DiscreteCDF
import SampLib.General.PiecewiseConstant
import SampLib.General.PiecewiseLinear

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

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (D : FiniteCDF.Model) (n : ℕ)
    (hl : D.lower = 0) (hu : D.upper = (n : ℤ) - 1)
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (DiscreteCDF.discreteCDF_distSpec E D n hl hu) F (measurable_of_countable _) R

example (E : CoPset) (D : PiecewiseConstant.Model) (F : ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (PiecewiseConstant.piecewiseConstant_distSpec E D) F (measurable_of_countable _) R

example (E : CoPset) (D : PiecewiseLinear.Model) (F : ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (PiecewiseLinear.piecewiseLinear_distSpec E D) F (measurable_of_countable _) R

end integer_draws

open MeasureTheory

private def plateau : FiniteCDF.Model where
  lower := 0
  upper := 3
  nonempty := by norm_num
  scale := 4
  positive := by norm_num
  cdf x := if x < 2 then 0 else 4
  monotone := by intro a ha b hb hab; dsimp; split_ifs <;> omega
  bounded := by intro x hx; dsimp; split_ifs <;> norm_num
  upper_mass := by norm_num

example : DiscreteCDF.cumulative plateau 4 = [0, 0, 4, 4] := by
  rfl

example : FiniteCDF.law plateau (Set.Iic 1) = 0 := by
  rw [FiniteCDF.cdf plateau 1 (by norm_num [plateau])]
  norm_num [plateau]

example : FiniteCDF.law plateau (Set.Iic 2) = 1 := by
  rw [FiniteCDF.cdf plateau 2 (by norm_num [plateau])]
  norm_num [plateau]

private def constantGrid : PiecewiseConstant.Model where
  points := [-1, 0, 2]
  heights := [2, 1]
  length := rfl
  increasing := by
    intro i hi
    have h : i < 2 := by simpa using hi
    interval_cases i <;> norm_num
  positive := by norm_num [PiecewiseConstant.weights]

example : PiecewiseConstant.weights constantGrid.points constantGrid.heights = [2, 2] := rfl

example : (∫⁻ _, (∞ : ℝ≥0∞) ∂PiecewiseConstant.law constantGrid) = ∞ := by simp

private def ramp : LinearBin.Model where
  left := -3
  width := 3
  positive_width := by norm_num
  ha := 0
  hb := 3
  positive_mass := by norm_num

example : List.ofFn (fun i : Fin 3 => LinearBin.height ramp i) = [0, 3, 6] := rfl

example : PiecewiseLinear.binWeight (-3, 0) (0, 3) = 6 := rfl
example : 2 * (0 + 3 + 6) = 3 * PiecewiseLinear.binWeight (-3, 0) (0, 3) := by
  exact PiecewiseLinear.binWeight_mass (-3, 0) (0, 3) (by norm_num)

example : (∫⁻ _, (∞ : ℝ≥0∞) ∂LinearBin.law ramp) = ∞ := by simp

private theorem constantGrid_expectation (F : ℤ → ℝ≥0∞) :
    (∫⁻ x, F x ∂PiecewiseConstant.law constantGrid) =
      (2 * F (-1) + (F 0 + F 1)) / 4 := by
  rw [← PiecewiseConstant.expectation, WeightedChoice.lintegral_law]
  norm_num only [constantGrid, PiecewiseConstant.weights, WeightedChoice.weightedSum,
    List.sum_cons, List.sum_nil, Nat.cast_ofNat, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.zero_add,
    Nat.reduceAdd, Histogram.binLaw, dite_true]
  simp only [← RndIntExcRange.expectation, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ]
  rw [ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]

example : (∫⁻ x, (if x = -1 then 1 else 0 : ℝ≥0∞)
    ∂PiecewiseConstant.law constantGrid) = 1 / 2 := by
  rw [constantGrid_expectation]
  norm_num
  rw [← one_div (2 : ℝ≥0∞)]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr
  norm_num

example : (∫⁻ x, (if x = 1 then 1 else 0 : ℝ≥0∞)
    ∂PiecewiseConstant.law constantGrid) = 1 / 4 := by
  rw [constantGrid_expectation]
  norm_num

private theorem ramp_mass :
    AcceptedProposal.mass (UniformInt.law ramp.width) (LinearBin.acceptance ramp) =
      (3 : ℝ≥0∞)⁻¹ := by
  rw [AcceptedProposal.mass, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ, LinearBin.acceptance, LinearBin.height,
    LinearBin.envelope, ramp, AcceptedProposal.weight, IntegerThreshold.bias, RationalCoin.bias]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

example : (∫⁻ x, (if x = -3 then ∞ else 0 : ℝ≥0∞) ∂LinearBin.law ramp) = 0 := by
  rw [LinearBin.law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [LinearBin.offsetLaw, AcceptedProposal.law, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), ramp_mass, UniformInt.lintegral_law]
  norm_num [Finset.sum_range_succ, LinearBin.acceptance, LinearBin.height,
    LinearBin.envelope, ramp, AcceptedProposal.weight, IntegerThreshold.bias, RationalCoin.bias]

#print axioms SampLib.DiscreteCDF.discreteCDF_distSpec
#print axioms SampLib.DiscreteCDF.twp_search
#print axioms SampLib.PiecewiseConstant.piecewiseConstant_distSpec
#print axioms SampLib.PiecewiseLinear.piecewiseLinear_distSpec
#print axioms SampLib.LinearBin.twp_draw
#print axioms SampLib.LinearGridMass.twice_sum
#print axioms SampLib.LinearBin.mass_ne_zero

end
end ReviewExpansionStructured
