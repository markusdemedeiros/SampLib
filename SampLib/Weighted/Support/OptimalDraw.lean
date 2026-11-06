import SampLib.Weighted.Support.OptimalWalk
import SampLib.Weighted.Syntax.OptimalSource
import SampLib.Weighted.Laws.OptimalRejection

/-! # Rejection restarts in the actual cyclic probability-matrix walk -/

open ProbLang
open scoped ENNReal

namespace SampLib.Optimal

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open OptimalEncoding OptimalMatrix

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ListValues.listVal_openRec Program.scan_openRec

/-- The complete cyclic traversal and optional rejection preserve the requested weighted law. -/
theorem twp_root (E : CoPset) (ws : List ℕ) (k l : ℕ) (hl : l < k)
    (hs : 0 < ws.sum) (hD : ws.sum ≤ denominator k l)
    (hupper : denominator k l ≤ 2 * ws.sum) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E (OptimalWalk.root (encoded ws k l) k l (rejectionIndex ws (denominator k l)))
        (OptimalWalk.post F) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  let C := ∫⁻ i, F i ∂WeightedChoice.law ws
  let R : IProp GF := iprop(↯ (2 * ε) -∗ ↯ C -∗
    tglWp E (OptimalWalk.root (encoded ws k l) k l (rejectionIndex ws (denominator k l)))
      (OptimalWalk.post F))
  have hRestart : R ⊢ ↯ (C + 2 * ε) -∗
      tglWp E (OptimalWalk.root (encoded ws k l) k l (rejectionIndex ws (denominator k l)))
        (OptimalWalk.post F) := by
    iintro IH Hbudget
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hbudget
    iapply IH $$ Hterm Hcredit
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (restart_expectation ws hl hs hD hupper F ε) $$ Htotal
  iapply OptimalWalk.twp_walk E (encoded ws k l) k l hl
    (rejectionIndex ws (denominator k l)) (encoded_root ws hl hD) F (C + 2 * ε) R
    hRestart $$ IH Hsample

/-- Opening the original direct-draw source exposes the verified cyclic root state. -/
theorem twp_optimalDraw (E : CoPset) (ws : List ℕ) (k l : ℕ) (hl : l < k)
    (hs : 0 < ws.sum) (hD : ws.sum ≤ denominator k l)
    (hupper : denominator k l ≤ 2 * ws.sum) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(Table.value (table ws k l) : Val rT).fst #()) (OptimalWalk.post F) := by
  iintro Hcredit
  rw [Program.draw_code_eq (rT := rT)]
  simp only [table, Table.value]
  rw [← encoded_rows ws k l]
  iterate 17 twp_pure
  ieval (
    change _ ⊢ tglWp E
      (OptimalWalk.root (rT := rT) (encoded ws k l) k l
        (rejectionIndex ws (denominator k l))) _)
  iapply twp_root (rT := rT) (GF := GF) E ws k l hl hs hD hupper F $$ Hcredit

end specification

end

end SampLib.Optimal
