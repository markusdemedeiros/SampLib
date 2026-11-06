import SampLib.Samplers.InclusionSplitting

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured005

noncomputable section

open SampLib

private def ws : List ℕ := [1, 2, 1]
private theorem total_pos : 0 < ws.sum := by decide
private theorem capacity : ∀ w ∈ ws, 2 * w ≤ ws.sum := by
  intro w hw
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> decide

private def start : SplittingPPS.State 3 2 :=
  SplittingPPS.State.initial ws 2 total_pos capacity

private theorem continues : start.amount < start.denominator := by decide
private def residual := start.next (by decide) (by decide) continues
private theorem finishes : ¬residual.amount < residual.denominator := by decide

/-- The exact ordered joint law differs from merely asserting inclusion marginals. -/
example : SplittingPPS.inputLaw ws 2 total_pos (by decide) capacity =
    (((1 : ℝ≥0∞) / 2) • MeasureTheory.Measure.dirac ([2, 1] : List ℤ)) +
    (((1 : ℝ≥0∞) / 2) • MeasureTheory.Measure.dirac ([0, 1] : List ℤ)) := by
  change SplittingPPS.law (by decide) (by decide) start = _
  rw [SplittingPPS.law_step _ _ start continues]
  have hfinish := SplittingPPS.law_done (by decide) (by decide) residual finishes
  change SplittingPPS.law _ _ (start.next _ _ continues) = _ at hfinish
  rw [hfinish]
  norm_num [start, residual, SplittingPPS.State.initial, SplittingPPS.State.amount,
    SplittingPPS.State.low, SplittingPPS.State.high, SplittingPPS.State.topLabels,
    SplittingPPS.State.next, ws, SplittingPPS.prepare, SplittingPPS.tag,
    SplittingPPS.adjust, SplittingPPS.trim, SplittingPPS.ordered,
    List.insertionSort_cons, List.orderedInsert, ENNReal.div_self]
  have hhalf : (2 : ℝ≥0∞) / 4 = 2⁻¹ := by
    simpa only [mul_one, show (2 : ℝ≥0∞) * 2 = 4 by norm_num, one_div] using
      (ENNReal.mul_div_mul_left 1 2 (c := 2) (by norm_num) (by simp))
  rw [hhalf]

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

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

example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_zero_distSpec E [])
    F (measurable_of_countable _) R

example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_zero_distSpec E [0, 0])
    F (measurable_of_countable _) R

section positive

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (weights : List ℕ) (count : ℕ) (ht : 0 < weights.sum)
    (hc : count ≤ weights.length) (hcap : ∀ w ∈ weights, count * w ≤ weights.sum)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_distSpec E weights count ht hc hcap)
    F (measurable_of_countable _) R

example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_distSpec E ws 2 total_pos (by decide) capacity)
    F (measurable_of_countable _) R

/-- A sparse interior population hits the terminal probability-one split immediately. -/
example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_distSpec E [0, 1] 1 (by decide) (by decide)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> decide)) F (measurable_of_countable _) R

example (E : CoPset) (R : IProp GF) :=
  frame (InclusionSplitting.inclusionSplitting_distSpec E [1, 1] 2 (by decide) (by decide)
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> decide)) (fun _ => ∞) measurable_const R

end positive
end callers

#print axioms SampLib.InclusionSplitting.inclusionSplitting_distSpec
#print axioms SampLib.InclusionSplitting.inclusionSplitting_zero_distSpec
#print axioms SampLib.SplittingPPS.input_inclusion_expectation
#print axioms SampLib.SplittingPPS.input_inclusion_probability
#print axioms SampLib.SplittingPPS.input_length
#print axioms SampLib.SplittingPPS.input_nodup

end
end ReviewExactStructured005
