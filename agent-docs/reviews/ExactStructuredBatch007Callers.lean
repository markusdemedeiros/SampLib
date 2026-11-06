import SampLib.Weighted.HanHoshi

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured007

noncomputable section

open SampLib

private def weights : List ℕ := [1, 0, 2]
private instance : NeZero weights.sum := ⟨by decide⟩

/-- A coarse cell straddles1/3; refined cells resolve on either side and skip the zero row. -/
example : HanHoshi.scan 3 1 4 weights 0 = none := by decide
example : HanHoshi.scan 3 1 8 weights 0 = some 0 := by decide
example : HanHoshi.scan 3 3 8 weights 0 = some 2 := by decide
example : HanHoshi.scan 3 7 8 weights 0 = some 2 := by decide

/-- Exact CDF-boundary contact certifies a half-open whole cell. -/
example : HanHoshi.scan 4 0 2 [2, 0, 2] 0 = some 0 := by decide
example : HanHoshi.scan 4 1 2 [2, 0, 2] 0 = some 2 := by decide

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂CategoricalCDF.law ws) ∗ R -∗
      tglWp E pl(&Occil.Weighted.hanHoshi &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (HanHoshi.hanHoshi_distSpec E ws).wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  itrivial

example (E : CoPset) (F : ℤ → ℝ≥0∞) (R : IProp GF) := framed E weights F R

example (E : CoPset) (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂CategoricalCDF.law [0, 0, 7, 0]) ∗ R -∗
      tglWp E pl(&Occil.Weighted.hanHoshi
        &(listVal (fun n : ℕ => Val.int n) [0, 0, 7, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  have : NeZero ([0, 0, 7, 0] : List ℕ).sum := ⟨by decide⟩
  exact framed E [0, 0, 7, 0] F R

example (E : CoPset) (R : IProp GF) := framed E weights (fun _ => ∞) R

end callers

#print axioms SampLib.HanHoshi.hanHoshi_distSpec
#print axioms SampLib.HanHoshi.bit_expectation
#print axioms SampLib.HanHoshi.unresolved_credit
#print axioms SampLib.RealCategoricalCDF.law_eq
#print axioms SampLib.FiniteBoundaryBands.expectation_preservation
#print axioms SampLib.FiniteBoundaryBands.exists_horizon
#print axioms framed

end
end ReviewExactStructured007
