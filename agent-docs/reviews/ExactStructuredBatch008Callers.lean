import SampLib.Weighted.KnuthYao

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured008

noncomputable section

open SampLib

private def weights : List ℕ := [0, 1, 0, 4]
private instance : NeZero weights.sum := ⟨by decide⟩
private def zeroCredit (i : ℕ) : ℝ≥0∞ := if i = 0 ∨ i = 2 then ∞ else 0

/-- Infinite credit on zero-weight rows still has exactly zero expected cost. -/
example : (∫⁻ i, zeroCredit i ∂WeightedChoice.law weights) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, weights, zeroCredit]

example : KnuthYao.certain [0, 0, 9, 0] 9 = some 2 := by decide
example : KnuthYao.certain weights 5 = none := by decide

/-- The canonical binary columns exhaust a dyadic law after its first bit. -/
example : KnuthYaoColumns.alive ([1, 0, 1] : List ℕ).get 2 1 = 0 := by decide
example : KnuthYaoColumns.columns ([1, 0, 1] : List ℕ).get 2 0 = [1, 0, 1] := by decide

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(&Occil.Weighted.knuthYao &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (KnuthYao.knuthYao_distSpec E ws).wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E weights F R
example (E : CoPset) (R : IProp GF) := framed E weights zeroCredit R
example (E : CoPset) (R : IProp GF) := framed E weights (fun _ => ∞) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [0, 0, 9, 0]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.knuthYao
        &(listVal (fun n : ℕ => Val.int n) [0, 0, 9, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([0, 0, 9, 0] : List ℕ).sum := ⟨by decide⟩
  exact framed E [0, 0, 9, 0] F R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law [1, 0, 1]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.knuthYao
        &(listVal (fun n : ℕ => Val.int n) [1, 0, 1]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([1, 0, 1] : List ℕ).sum := ⟨by decide⟩
  exact framed E [1, 0, 1] F R

end callers

#print axioms SampLib.KnuthYao.knuthYao_distSpec
#print axioms SampLib.KnuthYao.twp_loop
#print axioms SampLib.Ddg.twp_of_columns
#print axioms SampLib.DdgCredits.aggregate_le
#print axioms SampLib.KnuthYaoColumns.alive_succ
#print axioms SampLib.KnuthYaoColumns.row_expectation
#print axioms framed

end
end ReviewExactStructured008
