import SampLib.Weighted.FastLoadedDiceRoller
import SampLib.Weighted.SortedChoice

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured010

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private instance sorted_closed : ClosedExp (Occil.WeightedVariants.sortedChoice : Exp rT) where
  lc := by unfold Occil.WeightedVariants.sortedChoice; is_lc
  fv := by kernel_rfl

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

theorem fldr_framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (F : ℕ → ℝ≥0∞)
    (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun result => iprop(∃ i : ℕ, ⌜result = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((FastLoadedDice.fastLoadedDiceRoller_distSpec E ws).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HQ
  itrivial

theorem sorted_framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (hs : SortedWeights.Sorted ws) (F : ℕ → ℝ≥0∞) (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun result => iprop(∃ i : ℕ, ⌜result = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((SortedChoice.sortedChoice_distSpec E ws hs).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HQ
  itrivial

/-- FLDR then sortedChoice: the second call is paid conditionally on the first result. -/
theorem composed (E : CoPset) (ws vs : List ℕ) [NeZero ws.sum] [NeZero vs.sum]
    (hs : SortedWeights.Sorted vs) (G : ℕ → ℕ → ℝ≥0∞) (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, (∫⁻ j, G i j ∂WeightedChoice.law vs) ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
          &(listVal (fun n : ℕ => Val.int n) ws).fst #();
        &Occil.WeightedVariants.sortedChoice &(listVal (fun n : ℕ => Val.int n) vs).fst #())
        (fun result => iprop(∃ i j : ℕ, ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (G i j) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  twp_bind pl(&Occil.Weighted.fastLoadedDiceRoller
    &(listVal (fun n : ℕ => Val.int n) ws).fst #())
  iapply ((FastLoadedDice.fastLoadedDiceRoller_distSpec E ws).wp
    (fun i => ∫⁻ j, G i j ∂WeightedChoice.law vs) (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  twp_pure
  iapply ((SortedChoice.sortedChoice_distSpec E vs hs).wp
    (G i) (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  iexists i, j
  iframe Hcredit HQ
  itrivial

/-! ## FLDR boundaries: padding 3 → 4, no padding, certain rows, singleton. -/

example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([0, 1, 2, 0] : List ℕ).sum := ⟨by decide⟩
  exact fldr_framed E [0, 1, 2, 0] (fun _ => ∞) Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([1, 0, 3] : List ℕ).sum := ⟨by decide⟩
  exact fldr_framed E [1, 0, 3] F Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([0, 0, 9, 0] : List ℕ).sum := ⟨by decide⟩
  exact fldr_framed E [0, 0, 9, 0] F Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([5] : List ℕ).sum := ⟨by decide⟩
  exact fldr_framed E [5] F Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([3, 0, 0, 0, 0, 0, 0, 2] : List ℕ).sum := ⟨by decide⟩
  exact fldr_framed E [3, 0, 0, 0, 0, 0, 0, 2] F Q

/-! ## sortedChoice boundaries: both orientations, constants, zero groups, singleton. -/

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([4, 2, 1, 0] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [4, 2, 1, 0] (Or.inr (by decide)) F Q

example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([0, 0, 1, 3] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [0, 0, 1, 3] (Or.inl (by decide)) (fun _ => ∞) Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([2, 2, 2] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [2, 2, 2] (Or.inl (by decide)) F Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([3] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [3] (Or.inl (by decide)) F Q

/-- Only the first dyadic group has positive envelope; later FLDR rows are zero. -/
example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([5, 0, 0, 0, 0, 0, 0] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [5, 0, 0, 0, 0, 0, 0] (Or.inr (by decide)) (fun _ => ∞) Q

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([0, 0, 0, 0, 0, 0, 0, 0, 1] : List ℕ).sum := ⟨by decide⟩
  exact sorted_framed E [0, 0, 0, 0, 0, 0, 0, 0, 1] (Or.inl (by decide)) F Q

example (E : CoPset) (G : ℕ → ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([0, 1, 2, 0] : List ℕ).sum := ⟨by decide⟩
  have : NeZero ([9, 7, 7, 4, 2, 1, 0] : List ℕ).sum := ⟨by decide⟩
  exact composed E [0, 1, 2, 0] [9, 7, 7, 4, 2, 1, 0] (Or.inr (by decide)) G Q

end

open SampLib

/-! ## Pure checks: padding, envelopes and the excluded domain. -/

example : PowerOfTwoCeiling.width 3 = 4 ∧ PowerOfTwoCeiling.width 4 = 4 := by decide

/-- The single implicit padding row of [0,1,2,0] has width 1 = 4 - 3 in the dyadic matrix. -/
example : FastLoadedDiceCredits.augmented [0, 1, 2, 0] 4 = [0, 1, 2, 0, 1] := by decide

/-- Zero rows receive no mass even under infinite credit; the dummy label 4 is never output. -/
example : (∫⁻ i, (if i = 1 ∨ i = 2 then 0 else ∞) ∂WeightedChoice.law [0, 1, 2, 0]) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

/-- Groups {0}, {1,2}, {3..6} of [9,7,7,4,2,1,0] get envelopes 9, 2*7, 4*4. -/
example : SortedChoice.envelopes [9, 7, 7, 4, 2, 1, 0] false = [9, 14, 16] := by decide

example : SortedChoice.envelopes [5, 0, 0, 0, 0, 0, 0] false = [5, 0, 0] := by decide

/-- Unsorted lists, including equal endpoints, lie outside the domain (the source fails). -/
example : ¬ SortedWeights.Sorted [1, 2, 1] := by simp [SortedWeights.Sorted]
example : ¬ SortedWeights.Sorted [2, 0, 2] := by simp [SortedWeights.Sorted]

#print axioms SampLib.FastLoadedDice.fastLoadedDiceRoller_distSpec
#print axioms SampLib.FastLoadedDice.twp_loop
#print axioms SampLib.FastLoadedDiceCredits.expectation
#print axioms SampLib.SortedChoice.sortedChoice_distSpec
#print axioms SampLib.SortedChoice.twp_loop
#print axioms SampLib.SortedChoice.expectation_preservation
#print axioms fldr_framed
#print axioms sorted_framed
#print axioms composed

end ReviewExactStructured010
