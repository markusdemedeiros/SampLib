import SampLib.Weighted.Support.Ddg
import SampLib.Weighted.Support.DdgScan
import SampLib.Weighted.Laws.KnuthYaoCredits
import SampLib.Weighted.Syntax.KnuthYao

/-! # Symbolic execution of the actual Knuth–Yao walk -/

open ProbLang
open scoped ENNReal

namespace SampLib.KnuthYao

noncomputable section

open KnuthYaoColumns Program

private theorem source_column (ws : List ℕ) (T d : ℕ) :
    ws.map (fun w => DdgScan.digit w (2 ^ (d + 1)) T) = columns ws.get T d := by
  simpa only [DdgScan.digit] using (columns_list ws T d).symm

private theorem expanded_cast (rank : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (rank : ℤ) * 2 + b = ((2 * rank + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb, mul_comm]

private theorem doubled_cast (d : ℕ) :
    ((2 ^ (d + 1) : ℕ) : ℤ) * 2 = ((2 ^ ((d + 1) + 1) : ℕ) : ℤ) := by
  simp [pow_succ]

private theorem retained_lt (ws : List ℕ) (T : ℕ) (hT : 0 < T) (htotal : ws.sum = T)
    (d rank b rest : ℕ) (hr : rank < alive ws.get T d) (hb : b < 2)
    (hout : DdgScan.result (columns ws.get T d) (2 * rank + b) = .inr rest) :
    rest < alive ws.get T (d + 1) := by
  have hsum : ∑ i, ws.get i = T := by
    simpa only [← List.sum_ofFn, List.ofFn_get] using htotal
  have hw := alive_succ hT hsum d
  rw [← columns_sum] at hw
  have ho := DdgScan.result_bounds (columns ws.get T d) (2 * rank + b)
  rw [hout] at ho
  omega

@[pl_fold] private def expression {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (T d rank : ℕ) : Exp rT :=
  pl(&(loop ws T) #int ((2 ^ (d + 1) : ℕ) : ℤ) #int (rank : ℤ))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

/-- One bit, one deterministic column scan, then either a leaf or the next live rank. -/
private theorem twp_round (E : CoPset) (ws : List ℕ) (T : ℕ)
    (hT : 0 < T) (htotal : ws.sum = T) (F : ℕ → ℝ≥0∞) (h d : ℕ)
    (ih : ∀ rank, rank < alive ws.get T (d + 1) →
      ⊢ ↯ (DdgCredits.cutCredit (columns ws.get T) F h (d + 1) rank) -∗
        tglWp E (expression ws T (d + 1) rank)
          (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))))
    (rank : ℕ) (hr : rank < alive ws.get T d) :
    ⊢ ↯ (DdgCredits.cutCredit (columns ws.get T) F (h + 1) d rank) -∗
      tglWp E (expression ws T d rank)
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  simp only [expression, loop_eq]
  twp_pures
  twp_bind pl(rand(#2, #()))
  iapply (twp_rand_exp (ε₂ := fun b => DdgCredits.scan (columns ws.get T d)
    (2 * rank + b) F (DdgCredits.cutCredit (columns ws.get T) F h (d + 1)))
    (by decide) (bit_expectation ws.get T F h d rank).le) $$ Hcredit
  iintro %b ⟨%hb, Hcredit⟩
  simp only [Exp.ofVal]
  iterate 2 twp_pure
  rw [expanded_cast rank b hb.1]
  twp_pure
  twp_bind pl(&Occil.Weighted.matrixColumn
    &(listVal (fun w : ℕ => Val.int w) ws).fst #int ((2 ^ (d + 1) : ℕ) : ℤ)
    #int (T : ℤ) #int ((2 * rank + b.toNat : ℕ) : ℤ) #0)
  iapply tglWp_wand
  isplitl []
  · iapply DdgScan.twp_matrixColumn E ws (2 ^ (d + 1)) T (2 * rank + b.toNat) 0
  iintro %v %hv
  rw [source_column] at hv
  subst v
  isimp only [DdgScan.scan_eq] at Hcredit
  cases hout : DdgScan.result (columns ws.get T d) (2 * rank + b.toNat) with
  | inl i =>
    isimp only [hout] at Hcredit
    simp only [DdgScan.encode, Exp.ofVal, Nat.zero_add]
    twp_pures
    twp_value
    imodintro
    iexists i
    iframe Hcredit
    ipureintro
    rfl
  | inr rest =>
    isimp only [hout] at Hcredit
    simp only [DdgScan.encode, Exp.ofVal]
    iterate 3 twp_pure
    rw [doubled_cast]
    have hi := ih rest (retained_lt ws T hT htotal d rank b.toNat rest hr (by omega) hout)
    simp only [expression, loop_eq] at hi
    ieval (
      change _ ⊢ tglWp E
        pl(&(loopCode (listVal (fun w : ℕ => Val.int w) ws).fst T)
          #int ((2 ^ ((d + 1) + 1) : ℕ) : ℤ) #int (rest : ℤ)) _)
    iapply hi $$ Hcredit

/-- The full categorical continuation law for the non-certain branch of the original walk. -/
theorem twp_loop (E : CoPset) (ws : List ℕ) (hT : 0 < ws.sum)
    (hproper : ∀ i, ws.get i < ws.sum) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&(loop ws ws.sum) #2 #0)
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hsum : ∑ i, ws.get i = ws.sum := by rw [← List.sum_ofFn, List.ofFn_get]
  have hwidth (d : ℕ) : 2 * alive ws.get ws.sum d =
      (columns ws.get ws.sum d).sum + alive ws.get ws.sum (d + 1) := by
    rw [columns_sum]
    exact alive_succ hT hsum d
  iintro Hcredit
  isimp only [WeightedChoice.lintegral_law, ← row_zero_list ws hT hproper] at Hcredit
  ieval (change _ ⊢ tglWp E (expression ws ws.sum 0 0) _)
  iapply Ddg.twp_of_columns E (expression ws ws.sum) _ (columns ws.get ws.sum)
    (alive ws.get ws.sum) F hwidth (fun d => rowCredit ws.get ws.sum d F)
    (fun d => row_expectation ws.get ws.sum hT d F) ws.length
    (fun d => (alive_lt hT hsum d).le) (alive_zero hproper)
    (fun h d ih rank hr => twp_round E ws ws.sum hT rfl F h d ih rank hr)
    (by rfl) $$ Hcredit

end specification

end

end SampLib.KnuthYao
