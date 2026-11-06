import SampLib.Syntax.OptimalWalk
import SampLib.OptimalScan
import SampLib.Distributions.OptimalCredits
import SampLib.DdgContext

/-! # Symbolic execution of the actual cyclic matrix walk

The finite-depth DDG rule handles an arbitrarily long column traversal. Its
caller supplies the linear restart capability, consumed only at a rejection leaf.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.OptimalWalk

noncomputable section

open OptimalCyclic Optimal.Program

variable {n : ℕ}

@[pl_fold] private def expression {rT : Type} [ProbLangℝ rT]
    (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) (d rank : ℕ) : Exp rT :=
  pl(&(walkCode (listVal (fun m : ℕ => Val.int m) (List.ofFn rows)).fst k l rejected)
    #int (rank : ℤ) #int (column k l d : ℤ))

@[pl_fold] def root {rT : Type} [ProbLangℝ rT]
    (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) : Exp rT :=
  pl(&(walkCode (listVal (fun m : ℕ => Val.int m) (List.ofFn rows)).fst k l rejected) #0 #0)

private theorem expression_zero {rT : Type} [ProbLangℝ rT]
    (rows : Fin n → ℕ) {k l : ℕ} (hl : l < k) (rejected : ℤ) :
    expression rows k l rejected 0 0 = (root rows k l rejected : Exp rT) := by
  simp [expression, root, column_initial hl (by omega : 0 < k)]

private theorem source_column (rows : Fin n → ℕ) (k l d : ℕ) :
    (List.ofFn rows).map (fun m => OptimalScan.digit m (k - 1 - column k l d)) =
      columns rows k l d := by
  simp only [List.map_ofFn, columns, OptimalScan.digit, bit, Function.comp_def]

private theorem retained_lt (rows : Fin n → ℕ) (k l : ℕ)
    (hroot : ∑ i, tail k l (rows i) 0 = 1) (d rank b rest : ℕ)
    (hr : rank < alive rows k l d) (hb : b < 2)
    (hout : DdgScan.result (columns rows k l d) (2 * rank + b) = .inr rest) :
    rest < alive rows k l (d + 1) := by
  have hw := width rows k l hroot d
  have ho := DdgScan.result_bounds (columns rows k l d) (2 * rank + b)
  rw [hout] at ho
  omega

private theorem expanded_cast (rank : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    2 * (rank : ℤ) + b = ((2 * rank + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

private theorem position_cast {k l : ℕ} (hl : l < k) (d : ℕ) :
    (k : ℤ) - 1 - (column k l d : ℤ) = ((k - 1 - column k l d : ℕ) : ℤ) := by
  have h := column_lt hl d
  omega

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

/-- Returned natural labels carry the caller's prescribed continuation credit. -/
def post (F : ℕ → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_nextColumn (E : CoPset) {k l : ℕ} (hl : l < k) (d : ℕ) :
    ⊢ tglWp E pl(if #int (column k l d : ℤ) + #1 = #int (k : ℤ)
      then #int (l : ℤ) else #int (column k l d : ℤ) + #1)
      (fun v : Val rT => iprop(⌜v = Val.int (column k l (d + 1) : ℤ)⌝)) := by
  iterate 2 twp_pure
  rw [show (column k l d : ℤ) + 1 = ((column k l d + 1 : ℕ) : ℤ) by norm_cast, int_beq]
  by_cases h : column k l d + 1 = k
  · rw [beq_iff_eq.mpr (show ((column k l d + 1 : ℕ) : ℤ) = k by exact_mod_cast h)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [column_succ hl, h, ite_true]
  · rw [beq_eq_false_iff_ne.mpr
      (show ((column k l d + 1 : ℕ) : ℤ) ≠ k by exact_mod_cast h)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [column_succ hl, h, Nat.cast_add]

/-- One fair bit, one exact column scan, and one source branch. -/
private theorem twp_round (E : CoPset) (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ) (hroot : ∑ i, tail k l (rows i) 0 = 1)
    (F : ℕ → ℝ≥0∞) (restartCredit : ℝ≥0∞) (R : IProp GF)
    (hRestart : R ⊢ ↯ restartCredit -∗
      tglWp E (root rows k l rejected) (post F)) (h d : ℕ)
    (ih : ∀ rank, rank < alive rows k l (d + 1) →
      R ⊢ ↯ (DdgCredits.cutCredit (columns rows k l)
        (leafCredit rejected restartCredit F) h (d + 1) rank) -∗
        tglWp E (expression rows k l rejected (d + 1) rank) (post F))
    (rank : ℕ) (hr : rank < alive rows k l d) :
    R ⊢ ↯ (DdgCredits.cutCredit (columns rows k l)
      (leafCredit rejected restartCredit F) (h + 1) d rank) -∗
      tglWp E (expression rows k l rejected d rank) (post F) := by
  iintro HR Hcredit
  simp only [expression]
  twp_pures
  twp_bind pl(rand(#2, #()))
  iapply (twp_rand_exp (ε₂ := fun b => DdgCredits.scan (columns rows k l d)
    (2 * rank + b) (leafCredit rejected restartCredit F)
      (DdgCredits.cutCredit (columns rows k l)
        (leafCredit rejected restartCredit F) h (d + 1))) (by decide)
    (bit_expectation rows k l (leafCredit rejected restartCredit F) h d rank).le) $$ Hcredit
  iintro %b ⟨%hb, Hcredit⟩
  simp only [Exp.ofVal]
  iterate 2 twp_pure
  rw [expanded_cast rank b hb.1]
  iterate 3 twp_pure
  rw [position_cast hl d]
  twp_bind pl(&(Optimal.Program.scan : Exp rT)
    &(listVal (fun m : ℕ => Val.int m) (List.ofFn rows)).fst
    #int ((2 * rank + b.toNat : ℕ) : ℤ) #int ((k - 1 - column k l d : ℕ) : ℤ) #0)
  iapply tglWp_wand
  isplitl []
  · iapply OptimalScan.twp_scan E (List.ofFn rows) (k - 1 - column k l d) (2 * rank + b.toNat) 0
  iintro %v %hv
  rw [source_column] at hv
  subst v
  isimp only [DdgScan.scan_eq] at Hcredit
  cases hout : DdgScan.result (columns rows k l d) (2 * rank + b.toNat) with
  | inl i =>
    isimp only [hout] at Hcredit
    simp only [OptimalScan.encode, Exp.ofVal, Nat.zero_add]
    twp_pures
    rw [int_beq]
    by_cases hi : (i : ℤ) = rejected
    · rw [beq_iff_eq.mpr hi]
      isimp only [leafCredit, hi, ite_true] at Hcredit
      twp_pure
      ieval (change _ ⊢ tglWp E (root rows k l rejected) _)
      iapply hRestart $$ HR Hcredit
    · rw [beq_eq_false_iff_ne.mpr hi]
      isimp only [leafCredit, hi, ite_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      isimp only [post]
      iexists i
      iframe Hcredit
      itrivial
  | inr rest =>
    isimp only [hout] at Hcredit
    simp only [OptimalScan.encode, Exp.ofVal]
    iterate 3 twp_pure
    twp_bind pl(if #int (column k l d : ℤ) + #1 = #int (k : ℤ)
      then #int (l : ℤ) else #int (column k l d : ℤ) + #1)
    iapply tglWp_wand
    isplitl []
    · iapply twp_nextColumn E hl d
    iintro %v %hv
    subst v
    twp_pure
    have hi := ih rest (retained_lt rows k l hroot d rank b.toNat rest hr (by omega) hout)
    ieval (change _ ⊢ tglWp E (expression rows k l rejected (d + 1) rest) _)
    iapply hi $$ HR Hcredit

/-- An unbounded cyclic traversal retains the linear caller capability until a rejection leaf. -/
theorem twp_walk (E : CoPset) (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ) (hroot : ∑ i, tail k l (rows i) 0 = 1)
    (F : ℕ → ℝ≥0∞) (restartCredit : ℝ≥0∞) (R : IProp GF)
    (hRestart : R ⊢ ↯ restartCredit -∗ tglWp E (root rows k l rejected) (post F)) :
    R ⊢ ↯ (rowCredit rows k l 0 (leafCredit rejected restartCredit F)) -∗
      tglWp E (root rows k l rejected) (post F) := by
  have h := DdgContext.twp_of_columns E (expression rows k l rejected) (post F)
    (columns rows k l) (alive rows k l) (leafCredit rejected restartCredit F)
    (width rows k l hroot)
    (fun d => rowCredit rows k l d (leafCredit rejected restartCredit F))
    (fun d => row_expectation rows k l d (leafCredit rejected restartCredit F))
    n (alive_le rows k l hroot) rfl R
    (fun h d ih rank hr => twp_round E rows k l hl rejected hroot F restartCredit R
      hRestart h d ih rank hr) (by rfl)
  rwa [expression_zero rows hl rejected] at h

end specification

end

end SampLib.OptimalWalk
