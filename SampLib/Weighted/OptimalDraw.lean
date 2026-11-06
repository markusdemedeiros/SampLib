import SampLib.Weighted.Support.OptimalDraw
import SampLib.Weighted.Laws.OptimalTableLaw

/-! # Direct draws from an arbitrary valid cyclic probability table

The table holds integer rows scanned bitwise, the width `k`, the cycle start `l < k`
and a rejection label. Valid tables have total root mass one; the rejected row, if any,
has mass below one. The output is the remaining rows' categorical law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.OptimalTable

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open OptimalEncoding OptimalMatrix

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)
variable {n : ℕ}

attribute [local pl_step_simp] ListValues.listVal_openRec Optimal.Program.scan_openRec

/-- The cyclic traversal restarts on rejection with amplified termination credit. -/
theorem twp_root (E : CoPset) (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k) (rejected : ℤ)
    (hroot : ∑ i, weight k l (rows i) = denominator k l)
    (hA : 0 < acceptedMass rows k l rejected) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)) -∗
      tglWp E (OptimalWalk.root rows k l rejected) (OptimalWalk.post F) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor rows hl rejected hA) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  let C := ∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)
  let R : IProp GF := iprop(↯ (factor rows k l rejected * ε) -∗ ↯ C -∗
    tglWp E (OptimalWalk.root rows k l rejected) (OptimalWalk.post F))
  have hRestart : R ⊢ ↯ (C + factor rows k l rejected * ε) -∗
      tglWp E (OptimalWalk.root rows k l rejected) (OptimalWalk.post F) := by
    iintro IH Hbudget
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hbudget
    iapply IH $$ Hterm Hcredit
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (restart_expectation rows hl rejected hroot hA F ε) $$ Htotal
  iapply OptimalWalk.twp_walk E rows k l hl rejected (root_mass rows hl hroot) F
    (C + factor rows k l rejected * ε) R hRestart $$ IH Hsample

/-- Opening the original direct-draw source exposes the cyclic root state. -/
theorem twp_optimalDraw (E : CoPset) (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ) (hroot : ∑ i, weight k l (rows i) = denominator k l)
    (hA : 0 < acceptedMass rows k l rejected) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)) -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw
        &(Table.value ⟨List.ofFn rows, k, l, rejected⟩ : Val rT).fst #())
        (OptimalWalk.post F) := by
  iintro Hcredit
  rw [Optimal.Program.draw_code_eq (rT := rT)]
  simp only [Table.value]
  iterate 17 twp_pure
  ieval (change _ ⊢ tglWp E (OptimalWalk.root (rT := rT) rows k l rejected) _)
  iapply twp_root (rT := rT) (GF := GF) E rows k l hl rejected hroot hA F $$ Hcredit

/-- Every valid table: `l < k`, row numerators summing to `2^k - 2^l`, and positive
mass outside the rejection label. The law normalizes the accepted numerators. -/
theorem optimalDraw_distSpec (E : CoPset) (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ) (hroot : ∑ i, weight k l (rows i) = denominator k l)
    [NeZero (acceptedMass rows k l rejected)] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.optimalDraw
      &(Table.value ⟨List.ofFn rows, k, l, rejected⟩ : Val rT).fst #())
      (WeightedChoice.law (accepted rows k l rejected)) (fun i => Val.int (i : ℤ)) where
  spec F _ := by
    have h := twp_optimalDraw (rT := rT) (GF := GF) E rows k l hl rejected hroot
      (NeZero.pos _) F
    unfold OptimalWalk.post at h
    exact wand_entails h

end

end SampLib.OptimalTable
