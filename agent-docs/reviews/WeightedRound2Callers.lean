import SampLib.Samplers.FastLoadedDiceRoller
import SampLib.Samplers.SortedChoice
import SampLib.Samplers.OptimalChoice
import SampLib.Samplers.OptimalDraw

open ProbLang
open scoped ENNReal

namespace WeightedRound2Callers

noncomputable section

open SampLib

private def weights : List ℕ := [0, 1, 2, 0]
private instance : NeZero weights.sum := ⟨by decide⟩
private def zeroCredit (i : ℕ) : ℝ≥0∞ := if i = 1 ∨ i = 2 then 0 else ∞

/-- Infinite credit on zero rows and on the padded rejection label 4 costs nothing. -/
theorem zero_cost : (∫⁻ i, zeroCredit i ∂WeightedChoice.law weights) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, weights, zeroCredit]

/-- Total 3 pads to 4, leaving rejection mass 1/4; total 4 needs no padding. -/
example : PowerOfTwoCeiling.width 3 = 4 := by decide
example : PowerOfTwoCeiling.width 4 = 4 := by decide
example : PowerOfTwoCeiling.width 1 = 1 := by decide
example : KnuthYao.certain [0, 0, 9, 0] 9 = some 2 := by decide
example : KnuthYao.certain weights 3 = none := by decide

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (FastLoadedDice.fastLoadedDiceRoller_distSpec E ws).wp F
    (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

/-- Zero credit excludes zero rows and the implicit rejection label. -/
example (E : CoPset) (R : IProp GF) :
    ⊢ ↯ 0 ∗ R -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) weights).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (zeroCredit i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  ihave Hcredit := ErrorCredit.weaken zero_cost.le $$ Hcredit
  iapply framed E weights zeroCredit R $$ [Hcredit HR]
  iframe Hcredit HR

example (E : CoPset) (R : IProp GF) := framed E weights (fun _ => ∞) R

/-- A certain row, a power-of-two total and a singleton. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [0, 0, 9, 0]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) [0, 0, 9, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([0, 0, 9, 0] : List ℕ).sum := ⟨by decide⟩
  exact framed E [0, 0, 9, 0] F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [1, 0, 3]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) [1, 0, 3]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([1, 0, 3] : List ℕ).sum := ⟨by decide⟩
  exact framed E [1, 0, 3] F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [5]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) [5]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([5] : List ℕ).sum := ⟨by decide⟩
  exact framed E [5] F R

theorem sortedFramed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (hsorted : SortedWeights.Sorted ws) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (SortedChoice.sortedChoice_distSpec E ws hsorted).wp F
    (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

/-- Descending, ascending with zero rows, constant, singleton and a seven-element list
spanning three dyadic groups. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [4, 2, 1, 0]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) [4, 2, 1, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([4, 2, 1, 0] : List ℕ).sum := ⟨by decide⟩
  exact sortedFramed E [4, 2, 1, 0] (by unfold SortedWeights.Sorted; decide) F R

example (E : CoPset) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, (fun _ => ∞) i ∂WeightedChoice.law [0, 0, 1, 3]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) [0, 0, 1, 3]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ ∞ ∗ R)) := by
  have : NeZero ([0, 0, 1, 3] : List ℕ).sum := ⟨by decide⟩
  exact sortedFramed E [0, 0, 1, 3] (by unfold SortedWeights.Sorted; decide) (fun _ => ∞) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [2, 2, 2]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) [2, 2, 2]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([2, 2, 2] : List ℕ).sum := ⟨by decide⟩
  exact sortedFramed E [2, 2, 2] (by unfold SortedWeights.Sorted; decide) F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [3]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) [3]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([3] : List ℕ).sum := ⟨by decide⟩
  exact sortedFramed E [3] (by unfold SortedWeights.Sorted; decide) F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [9, 7, 7, 4, 2, 1, 0]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.sortedChoice
        &(listVal (fun n : ℕ => Val.int n) [9, 7, 7, 4, 2, 1, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([9, 7, 7, 4, 2, 1, 0] : List ℕ).sum := ⟨by decide⟩
  exact sortedFramed E [9, 7, 7, 4, 2, 1, 0] (by unfold SortedWeights.Sorted; decide) F R

theorem optimalFramed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice &(Optimal.listValNatInts ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (Optimal.optimalChoice_distSpec E ws).wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

/-- The direct draw on the table generated from the same weights. -/
theorem optimalDrawFramed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value (OptimalMatrix.create ws) : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (Optimal.optimalDraw_distSpec E ws).wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

/-- Certain rows (the repaired endpoint), zero rows, a singleton and a non-dyadic law. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [2, 0]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice &(Optimal.listValNatInts [2, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([2, 0] : List ℕ).sum := ⟨by decide⟩
  exact optimalFramed E [2, 0] F R

example (E : CoPset) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, (fun _ => ∞) i ∂WeightedChoice.law [0, 2]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice &(Optimal.listValNatInts [0, 2]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ ∞ ∗ R)) := by
  have : NeZero ([0, 2] : List ℕ).sum := ⟨by decide⟩
  exact optimalFramed E [0, 2] (fun _ => ∞) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [7]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice &(Optimal.listValNatInts [7]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([7] : List ℕ).sum := ⟨by decide⟩
  exact optimalFramed E [7] F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [1, 0, 2, 3]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice
        &(Optimal.listValNatInts [1, 0, 2, 3]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([1, 0, 2, 3] : List ℕ).sum := ⟨by decide⟩
  exact optimalFramed E [1, 0, 2, 3] F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [0, 3, 0]) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value (OptimalMatrix.create [0, 3, 0]) : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([0, 3, 0] : List ℕ).sum := ⟨by decide⟩
  exact optimalDrawFramed E [0, 3, 0] F R

/-- General tables: arbitrary rows, a rejection label and unreduced row bits. -/
theorem tableFramed (E : CoPset) {n : ℕ} (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ)
    (hroot : ∑ i, OptimalTable.weight k l (rows i) = OptimalEncoding.denominator k l)
    [NeZero (OptimalTable.acceptedMass rows k l rejected)] (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (OptimalTable.accepted rows k l rejected)) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value ⟨List.ofFn rows, k, l, rejected⟩ : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (OptimalTable.optimalDraw_distSpec E rows k l hl rejected hroot).wp F
    (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

/-- k=3, l=1, D=6: rows 9≡1, 2, 3 with label 2 rejected (mass 1/2). -/
example : OptimalTable.accepted ![9, 2, 3] 3 1 2 = [1, 2, 0] := by decide

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (OptimalTable.accepted ![9, 2, 3] 3 1 2)) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value ⟨List.ofFn ![9, 2, 3], 3, 1, 2⟩ : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero (OptimalTable.acceptedMass ![9, 2, 3] 3 1 2) := ⟨by decide⟩
  exact tableFramed E ![9, 2, 3] 3 1 (by decide) 2 (by decide) F R

/-- Rejection mass 5/6 (beyond one half), and the all-ones certain row with no rejection. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (OptimalTable.accepted ![1, 6] 3 1 1)) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value ⟨List.ofFn ![1, 6], 3, 1, 1⟩ : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero (OptimalTable.acceptedMass ![1, 6] 3 1 1) := ⟨by decide⟩
  exact tableFramed E ![1, 6] 3 1 (by decide) 1 (by decide) F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (OptimalTable.accepted ![0, 7] 3 1 (-1))) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(OptimalMatrix.Table.value ⟨List.ofFn ![0, 7], 3, 1, -1⟩ : Val rT).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero (OptimalTable.acceptedMass ![0, 7] 3 1 (-1)) := ⟨by decide⟩
  exact tableFramed E ![0, 7] 3 1 (by decide) (-1) (by decide) F R

/-- An unsorted list is outside the domain: the source fails on it. -/
example : ¬ SortedWeights.Sorted [1, 3, 2] := by unfold SortedWeights.Sorted; decide

end callers

#print axioms SampLib.FastLoadedDice.fastLoadedDiceRoller_distSpec
#print axioms SampLib.FastLoadedDice.twp_loop
#print axioms SampLib.FastLoadedDice.twp_scan
#print axioms SampLib.FastLoadedDiceCredits.expectation
#print axioms SampLib.DdgContext.twp_of_columns
#print axioms framed
#print axioms SampLib.SortedChoice.sortedChoice_distSpec
#print axioms SampLib.SortedChoice.twp_loop
#print axioms SampLib.SortedChoice.expectation_preservation
#print axioms sortedFramed
#print axioms SampLib.Optimal.optimalChoice_distSpec
#print axioms SampLib.Optimal.optimalDraw_distSpec
#print axioms SampLib.Optimal.twp_root
#print axioms optimalFramed
#print axioms optimalDrawFramed
#print axioms SampLib.OptimalTable.optimalDraw_distSpec
#print axioms SampLib.OptimalTable.restart_expectation
#print axioms tableFramed

end
end WeightedRound2Callers
