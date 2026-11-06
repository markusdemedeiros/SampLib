import SampLib.Samplers.OptimalChoice

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured011

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The public spec composes with an arbitrary framed resource and arbitrary credit. -/
theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (F : ℕ → ℝ≥0∞) (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice
        &(listVal (fun n : ℕ => Val.int (n : ℤ)) ws).fst #())
        (fun result => iprop(∃ i : ℕ, ⌜result = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((Optimal.optimalChoice_distSpec E ws).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HQ
  itrivial

/-- Sequential composition: two independent draws, the second funded per first outcome. -/
theorem twice (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (G : ℕ → ℕ → ℝ≥0∞)
    (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, ∫⁻ j, G i j ∂WeightedChoice.law ws ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.WeightedVariants.optimalChoice
        &(listVal (fun n : ℕ => Val.int (n : ℤ)) ws).fst #())
        (fun first => iprop(∃ i : ℕ, ⌜first = Val.int (i : ℤ)⌝ ∗ Q ∗
          tglWp E pl(&Occil.WeightedVariants.optimalChoice
            &(listVal (fun n : ℕ => Val.int (n : ℤ)) ws).fst #())
            (fun second => iprop(∃ j : ℕ, ⌜second = Val.int (j : ℤ)⌝ ∗ ↯ (G i j))))) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((Optimal.optimalChoice_distSpec E ws).wp
    (fun i => ∫⁻ j, G i j ∂WeightedChoice.law ws) (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  isplitl []
  · itrivial
  isplitl [HQ]
  · iexact HQ
  iapply ((Optimal.optimalChoice_distSpec E ws).wp
    (G i) (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  iexists j
  iframe Hcredit
  itrivial

/-- Certain row with a zero row: total 2 selects k = 2, l = 1 and the repaired endpoint. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([2, 0] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [2, 0] F Q

/-- Certain row behind a zero row, with infinite credit everywhere. -/
example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([0, 0, 5] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [0, 0, 5] (fun _ => ∞) Q

/-- Length-one shortcut. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([7] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [7] F Q

/-- Non-dyadic, padded total 5 (rejection row appended). -/
example (E : CoPset) (G : ℕ → ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([1, 0, 4] : List ℕ).sum := ⟨by norm_num⟩
  exact twice E [1, 0, 4] G Q

end

open SampLib OptimalMatrix

/-- [2, 0]: width 2, cycle start 1, all-ones certain row, no rejection label. -/
example : (create [2, 0]).rows = [3, 0] ∧ (create [2, 0]).width = 2 ∧
    (create [2, 0]).loopStart = 1 ∧ (create [2, 0]).rejected = -1 := by decide +kernel

/-- [1, 0, 4]: total 5 pads to denominator 6 = 2^3 - 2^1 with rejection label 3. -/
example : (create [1, 0, 4]).rows = [1, 0, 5, 1] ∧ (create [1, 0, 4]).width = 3 ∧
    (create [1, 0, 4]).loopStart = 1 ∧ (create [1, 0, 4]).rejected = 3 := by decide +kernel

/-- Exact total 6 = 2^3 - 2^1 needs no rejection row. -/
example : (create [3, 3]).rejected = -1 := by decide +kernel

/-- Infinite credit on zero-weight labels and the padding label costs nothing. -/
example : (∫⁻ i, (if i = 1 ∨ i = 3 then ∞ else 0) ∂WeightedChoice.law [1, 0, 4]) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

#print axioms SampLib.Optimal.optimalChoice_distSpec
#print axioms SampLib.Optimal.optimalDraw_distSpec
#print axioms SampLib.Optimal.twp_optimalMatrix
#print axioms SampLib.Optimal.twp_root
#print axioms SampLib.OptimalWalk.twp_walk
#print axioms SampLib.OptimalMatrix.restart_expectation
#print axioms ReviewExactStructured011.framed
#print axioms ReviewExactStructured011.twice

end ReviewExactStructured011
