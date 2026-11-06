import SampLib.Samplers.KnuthYao

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.ExactKnuthYaoCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (F : ℕ → ℝ≥0∞)
    (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws)) ⊢
      tglWp E pl(&Occil.Weighted.knuthYao &(listVal (fun w : ℕ => Val.int w) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ P ∗ ↯ (F i))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((KnuthYao.knuthYao_distSpec E ws).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe HP Hcredit
  itrivial

local instance : NeZero ([0, 2, 3, 0] : List ℕ).sum := ⟨by decide⟩
local instance : NeZero ([0, 7, 0] : List ℕ).sum := ⟨by decide⟩
local instance : NeZero ([1, 1] : List ℕ).sum := ⟨by decide⟩

private def zeroRows (i : ℕ) : ℝ≥0∞ := if i = 0 ∨ i = 3 then ∞ else 0

example : (∫⁻ i, zeroRows i ∂WeightedChoice.law [0, 2, 3, 0]) = 0 := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum, zeroRows]

theorem zeros_with_infinite_credit (E : CoPset) (P : IProp GF) :
    iprop(P ∗ ↯ 0) ⊢
      tglWp E pl(&Occil.Weighted.knuthYao
        &(listVal (fun w : ℕ => Val.int w) [0, 2, 3, 0]).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ P ∗ ↯ (zeroRows i))) := by
  have hz : (∫⁻ i, zeroRows i ∂WeightedChoice.law [0, 2, 3, 0]) = 0 := by
    simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum, zeroRows]
  simpa only [hz] using framed E [0, 2, 3, 0] zeroRows P

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.knuthYao &(listVal (fun w : ℕ => Val.int w) [0, 7, 0]).fst #())
      (WeightedChoice.law [0, 7, 0]) (fun i => Val.int (i : ℤ)) :=
  KnuthYao.knuthYao_distSpec E [0, 7, 0]

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.knuthYao &(listVal (fun w : ℕ => Val.int w) [1, 1]).fst #())
      (WeightedChoice.law [1, 1]) (fun i => Val.int (i : ℤ)) :=
  KnuthYao.knuthYao_distSpec E [1, 1]

#print axioms KnuthYao.knuthYao_distSpec
#print axioms KnuthYao.twp_loop
#print axioms KnuthYaoColumns.row_expectation
#print axioms Ddg.twp_of_columns
#print axioms DdgScan.twp_matrixColumn
#print axioms framed
#print axioms zeros_with_infinite_credit

end

end SampLib.ExactKnuthYaoCallers
