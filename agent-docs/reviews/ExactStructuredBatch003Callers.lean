import SampLib.Weighted.InclusionSystematic

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured003

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
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

/-- Empty and zero-mass populations admit the deterministic zero-count request. -/
example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSystematic.inclusionSystematic_zero_distSpec (GF := GF) E [])
    F (measurable_of_countable _) R

example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSystematic.inclusionSystematic_zero_distSpec (GF := GF) E [0, 0])
    F (measurable_of_countable _) R

section positive

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (count : ℕ)
    (hcount : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSystematic.inclusionSystematic_distSpec E ws count hcount hcap)
    F (measurable_of_countable _) R

local instance : NeZero ([1, 2, 1] : List ℕ).sum := ⟨by decide⟩

private theorem capacity : ∀ w ∈ ([1, 2, 1] : List ℕ), 2 * w ≤ [1, 2, 1].sum := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> norm_num

/-- A boundary-capacity category is selected with probability one. -/
example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSystematic.inclusionSystematic_distSpec E [1, 2, 1] 2
    (by decide) capacity) F (measurable_of_countable _) R

example : SystematicPPS.law [1, 2, 1] 2 {xs | (1 : ℤ) ∈ xs} = 1 := by
  have h := SystematicPPS.inclusion_probability [1, 2, 1] 2 1
    (by decide) (by decide) capacity
  norm_num at h
  exact h.trans (ENNReal.div_self (by norm_num) (by simp))

example : SystematicPPS.law [1, 2, 1] 2 {xs | (0 : ℤ) ∈ xs} = 1 / 2 := by
  have h := SystematicPPS.inclusion_probability [1, 2, 1] 2 0
    (by decide) (by decide) capacity
  norm_num at h
  apply h.trans
  simpa only [mul_one, show (2 : ℝ≥0∞) * 2 = 4 by norm_num] using
    (ENNReal.mul_div_mul_left 1 2 (c := 2) (by norm_num) (by simp))

/-- The two edge categories cannot occur together, despite positive marginals. -/
example : SystematicPPS.law [1, 2, 1] 2 {xs | (0 : ℤ) ∈ xs ∧ (2 : ℤ) ∈ xs} = 0 := by
  rw [← MeasureTheory.lintegral_indicator_one ((Set.to_countable _).measurableSet),
    SystematicPPS.expectation]
  norm_num only [List.sum_cons, List.sum_nil, Set.indicator_apply, Pi.one_apply]
  norm_num [SystematicPPS.select, Finset.sum_range_succ]
  intro ticket ht
  interval_cases ticket <;> norm_num

example (ticket : ℕ) (ht : ticket < 4) :
    (SystematicPPS.select 2 4 ticket [1, 2, 1] 0 0).length = 2 :=
  SystematicPPS.sample_length [1, 2, 1] 2 ticket (by decide) ht capacity

local instance : NeZero ([0, 1, 1, 0] : List ℕ).sum := ⟨by decide⟩

private theorem sparse_capacity : ∀ w ∈ ([0, 1, 1, 0] : List ℕ),
    1 * w ≤ [0, 1, 1, 0].sum := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> norm_num

/-- A nonempty sample skips zero-weight categories at both ends. -/
example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (InclusionSystematic.inclusionSystematic_distSpec E [0, 1, 1, 0] 1
    (by decide) sparse_capacity) F (measurable_of_countable _) R

end positive

#print axioms SampLib.InclusionSystematic.inclusionSystematic_distSpec
#print axioms SampLib.InclusionSystematic.inclusionSystematic_zero_distSpec
#print axioms SampLib.SystematicPPS.sample_length
#print axioms SampLib.SystematicPPS.inclusion_probability

end

end ReviewExactStructured003
