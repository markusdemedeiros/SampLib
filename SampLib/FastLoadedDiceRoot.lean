import SampLib.FastLoadedDiceLoop

/-! # Restart credit and the complete FLDR matrix walk -/

open ProbLang Finset
open scoped NNReal ENNReal

namespace SampLib.FastLoadedDice

noncomputable section

open FastLoadedDiceCredits

private theorem proper_matrix (ws : List ℕ) (k : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ 2 ^ k) (hproper : ∀ i, ws.get i < ws.sum) :
    ∀ i, matrix ws k i < 2 ^ k := by
  have hm : ∀ w ∈ ws, w < ws.sum := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
    exact hproper i
  intro i
  exact FldrDyadic.padded_lt ws (2 ^ k) hT hP hm _ (List.get_mem _ _)

/-- The padded matrix's root credit fits the original continuation plus one retry budget. -/
private theorem root_budget (ws : List ℕ) (k : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ 2 ^ k) (hdouble : 2 ^ k ≤ 2 * ws.sum)
    (hproper : ∀ i, ws.get i < ws.sum) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    KnuthYaoColumns.rowCredit (matrix ws k) (2 ^ k) 0 (extended ws F ε) ≤ credit ws F + ε := by
  rw [KnuthYaoColumns.row_zero (matrix ws k) (2 ^ k) (by positivity)
    (proper_matrix ws k hT hP hproper)]
  rw [← KnuthYaoColumns.weightedSum_ofFn, List.ofFn_get]
  exact expectation ws (2 ^ k) hT hP hdouble F ε

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_pass (E : CoPset) (ws : List ℕ) (k : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ 2 ^ k) (hproper : ∀ i, ws.get i < ws.sum)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (R : IProp GF)
    (restart : R ⊢ ↯ (credit ws F + 2 * ε) -∗
      tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F)) :
    R ⊢ ↯ (KnuthYaoColumns.rowCredit (matrix ws k) (2 ^ k) 0 (extended ws F ε)) -∗
      tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F) := by
  have hsum : ∑ i, matrix ws k i = 2 ^ k := by
    rw [← List.sum_ofFn, List.ofFn_get]
    exact augmented_sum ws (2 ^ k) hP
  have hwidth (d : ℕ) : 2 * alive ws k d = (columns ws k d).sum + alive ws k (d + 1) := by
    rw [KnuthYaoColumns.columns_sum]
    exact KnuthYaoColumns.alive_succ (by positivity) hsum d
  iintro HR Hcredit
  ieval (change _ ⊢ tglWp E (expression ws k 0 0) (resultPost F))
  iapply DdgContext.twp_of_columns E (expression ws k) (resultPost F) (columns ws k)
    (alive ws k) (extended ws F ε) hwidth
    (fun d => KnuthYaoColumns.rowCredit (matrix ws k) (2 ^ k) d (extended ws F ε))
    (fun d => KnuthYaoColumns.row_expectation (matrix ws k) (2 ^ k) (by positivity) d _)
    (augmented ws (2 ^ k)).length
    (fun d => (KnuthYaoColumns.alive_lt (by positivity) hsum d).le)
    (KnuthYaoColumns.alive_zero (proper_matrix ws k hT hP hproper)) R
    (fun h d ih rank hr => twp_round E ws k hP F ε R restart h d ih rank hr)
    (by rfl) $$ HR Hcredit

private def property (E : CoPset) (ws : List ℕ) (k : ℕ) (F : ℕ → ℝ≥0∞) : IProp GF :=
  iprop(↯ (credit ws F) -∗ tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F))

/-- Rejection consumes the larger restart budget; the implicit row has mass at most one half. -/
private theorem twp_property (E : CoPset) (ws : List ℕ) (k : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ 2 ^ k) (hdouble : 2 ^ k ≤ 2 * ws.sum)
    (hproper : ∀ i, ws.get i < ws.sum) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    iprop(↯ ε) ⊢ property E ws k F := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [property]
  iintro Hcredit
  isimp only [property, ENNReal.coe_ofNat] at IH
  ihave Hrestart : (↯ (credit ws F + 2 * ε) -∗
    tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F)) $$ [IH]
  · iintro Hretry
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hretry
    iapply IH $$ Hterm Hcredit
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (root_budget ws k hT hP hdouble hproper F ε) $$ Htotal
  iapply twp_pass E ws k hT hP hproper F ε _ (by iintro HR; iexact HR) $$ Hrestart Hsample

/-- Complete matrix traversal with the original categorical continuation credit. -/
theorem twp_loop (E : CoPset) (ws : List ℕ) (k : ℕ) (hT : 0 < ws.sum)
    (hP : ws.sum ≤ 2 ^ k) (hdouble : 2 ^ k ≤ 2 * ws.sum)
    (hproper : ∀ i, ws.get i < ws.sum) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit ws F) -∗ tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_property E ws k hT hP hdouble hproper F ε hε $$ Hterm
  isimp only [property] at Hnext
  iapply Hnext $$ Hcredit

end specification

end

end SampLib.FastLoadedDice
