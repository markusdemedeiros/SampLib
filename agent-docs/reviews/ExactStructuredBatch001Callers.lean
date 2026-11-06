import SampLib.Samplers.MarkovChain
import SampLib.Samplers.ShapeRejection

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The public continuation rule preserves an arbitrary caller resource and credit. -/
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

section transitions

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (rows : List MarkovChain.Row) (i : ℕ) (hi : i < rows.length)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (MarkovChain.markovStep_distSpec (GF := GF) E rows i hi)
    F (measurable_of_countable _) R

/-- Unequal row lengths and zero weights are allowed for one transition. -/
private def rows : List MarkovChain.Row :=
  [⟨[0, 3, 0], by decide⟩, ⟨[2], by decide⟩]

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (MarkovChain.markovStep_distSpec (GF := GF) E rows 0 (by decide))
    F (measurable_of_countable _) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (MarkovChain.markovStep_distSpec (GF := GF) E rows 1 (by decide))
    F (measurable_of_countable _) R

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.General.markovStep &(listVal MarkovChain.encodeRow rows).fst #0)
    (MarkovChain.kernel rows 0) (fun j : ℕ => Val.int j) :=
  MarkovChain.markovStep_distSpec E rows 0 (by decide)

end transitions

section shapes

variable {α : Type _} [MeasurableSpace α]

example (E : CoPset) (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Set α) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (hmass : μ s ≠ 0)
    (encode : α → Val rT) (proposal member : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (hmember : ∀ x, ⊢ tglWp E pl(&member.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  frame (ShapeRejection.shapeRejection_distSpec E μ s hs hmass encode
    proposal member hproposal hmember) F hF R

private def acceptAll : Val rT :=
  ⟨.lam (.lit (.bool true)), .lam (by is_lc), by is_lc⟩

/-- Acceptance mass one is included without a uniform-integer assumption. -/
theorem full_shape (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) (proposal : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂Rejection.law μ Set.univ (by simp)) ∗ R -∗
      tglWp E pl(&Occil.General.shapeRejection &proposal.fst &(acceptAll).fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  apply frame (ShapeRejection.shapeRejection_distSpec E μ Set.univ
    MeasurableSet.univ (by simp) encode proposal acceptAll hproposal ?_) F hF R
  intro x
  simp only [acceptAll, Set.mem_univ, decide_true]
  twp_pures
  twp_value
  imodintro
  itrivial

end shapes

#print axioms SampLib.MarkovChain.markovStep_distSpec
#print axioms SampLib.ShapeRejection.shapeRejection_distSpec
#print axioms SampLib.Rejection.expectation_preservation
#print axioms full_shape

end

end ReviewExactStructured001
