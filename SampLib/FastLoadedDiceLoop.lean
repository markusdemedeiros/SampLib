import SampLib.FastLoadedDiceScan
import SampLib.DdgContext

/-! # The actual dyadic matrix walk, with a linear restart capability -/

open ProbLang Finset
open scoped ENNReal

namespace SampLib.FastLoadedDice

noncomputable section

open FastLoadedDiceCredits FastLoadedDiceScan

abbrev matrix (ws : List ℕ) (k : ℕ) := (augmented ws (2 ^ k)).get
abbrev columns (ws : List ℕ) (k : ℕ) := KnuthYaoColumns.columns (matrix ws k) (2 ^ k)
abbrev alive (ws : List ℕ) (k : ℕ) := KnuthYaoColumns.alive (matrix ws k) (2 ^ k)

private theorem matrix_sum (ws : List ℕ) (k : ℕ) (hP : ws.sum ≤ 2 ^ k) :
    ∑ i, matrix ws k i = 2 ^ k := by
  rw [← List.sum_ofFn, List.ofFn_get]
  exact augmented_sum ws (2 ^ k) hP

private theorem depth_lt (ws : List ℕ) (k : ℕ) (hP : ws.sum ≤ 2 ^ k)
    (d rank : ℕ) (hr : rank < alive ws k d) : d < k := by
  by_contra hd
  have hzero := FldrDyadic.alive_zero (matrix ws k) k d (matrix_sum ws k hP) (by omega)
  change alive ws k d = 0 at hzero
  omega

private theorem scan_range (ws : List ℕ) (k : ℕ) (hP : ws.sum ≤ 2 ^ k)
    (d rank b : ℕ) (hr : rank < alive ws k d) (hb : b < 2) :
    2 * rank + b <
      (bits ws (FldrDyadic.place k d) ++ [dummy (2 ^ k) ws.sum (FldrDyadic.place k d)]).sum +
        alive ws k (d + 1) := by
  rw [source_columns ws k d (depth_lt ws k hP d rank hr)]
  have hw := KnuthYaoColumns.alive_succ (by positivity : 0 < 2 ^ k)
    (matrix_sum ws k hP) d
  rw [← KnuthYaoColumns.columns_sum] at hw
  change 2 * alive ws k d = (columns ws k d).sum + alive ws k (d + 1) at hw
  exact (show 2 * rank + b < 2 * alive ws k d by omega).trans_eq hw

private theorem expanded_cast (rank : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (rank : ℤ) * 2 + b = ((2 * rank + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb, mul_comm]

private theorem positive_test (place : ℕ) (hplace : 0 < place) :
    decide ((place : ℤ) ≤ 0) = false := decide_eq_false (by omega)

@[pl_fold] def expression {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (k d rank : ℕ) : Exp rT :=
  run ws (2 ^ k) (FldrDyadic.place k d) rank

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_expanded (E : CoPset) (rank : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    ⊢ tglWp E pl(#int (rank : ℤ) * #2 + #int b)
      (fun v : Val rT => iprop(⌜v = Val.int ((2 * rank + b.toNat : ℕ) : ℤ)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  change (Exp.lit (.int ((rank : ℤ) * 2 + b)) : Exp rT) =
    Exp.lit (.int ((2 * rank + b.toNat : ℕ) : ℤ))
  rw [expanded_cast rank b hb]

omit [ProbLangDist.IsUniformInt rT] in
/-- Deterministic completion of one sampled bit and the ensuing exact column scan. -/
private theorem twp_after_bit (E : CoPset) (ws : List ℕ) (k : ℕ) (hP : ws.sum ≤ 2 ^ k)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (R : IProp GF)
    (restart : R ⊢ ↯ (credit ws F + 2 * ε) -∗
      tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F))
    (h d : ℕ)
    (ih : ∀ rank, rank < alive ws k (d + 1) →
      R ⊢ ↯ (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1) rank) -∗
        tglWp E (expression ws k (d + 1) rank) (resultPost F))
    (rank : ℕ) (hr : rank < alive ws k d) (b : ℤ) (hb : 0 ≤ b ∧ b < 2) :
    R ⊢ ↯ (DdgCredits.scan (columns ws k d) (2 * rank + b.toNat) (extended ws F ε)
      (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1))) -∗
      tglWp E (Program.afterRandClosed ws (2 ^ k) ws.sum (FldrDyadic.place k d) rank b)
        (resultPost F) := by
  have hd := depth_lt ws k hP d rank hr
  have hplace := FldrDyadic.place_pos k d hd
  iintro HR Hcredit
  twp_bind pl(#int (rank : ℤ) * #2 + #int b)
  iapply tglWp_wand
  isplitl []
  · iapply twp_expanded E rank b hb.1
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  ieval (
    change _ ⊢ tglWp E
      (Program.afterBit ws (2 ^ k) ws.sum (FldrDyadic.place k d)
        (2 * rank + b.toNat)) (resultPost F))
  twp_pure
  twp_pure
  twp_pure
  rw [positive_test (FldrDyadic.place k d) hplace]
  twp_pure
  ieval (
    change _ ⊢ tglWp E pl(&(Program.scan ws (2 ^ k) ws.sum (FldrDyadic.place k d))
      &(listVal (fun w : ℕ => Val.int w) ws).fst
      #int ((2 * rank + b.toNat : ℕ) : ℤ) #0) (resultPost F))
  have hkernel : kernel ws (2 ^ k) (FldrDyadic.place k d) F ε
      (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1)) ws
      (2 * rank + b.toNat) 0 = DdgCredits.scan (columns ws k d) (2 * rank + b.toNat)
        (extended ws F ε) (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1)) := by
    simp only [kernel, Nat.zero_add, source_columns ws k d hd]
  isimp only [← hkernel] at Hcredit
  have advance (rest : ℕ) (hrest : rest < alive ws k (d + 1)) :
      R ⊢ ↯ (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1) rest) -∗
        tglWp E (run ws (2 ^ k) (FldrDyadic.place k d / 2) rest) (resultPost F) := by
    simpa only [FldrDyadic.place_half, expression] using ih rest hrest
  iapply twp_scan E ws (2 ^ k) (FldrDyadic.place k d) hP F ε _ (alive ws k (d + 1)) R
    restart advance ws (2 * rank + b.toNat) 0 (by omega)
    (scan_range ws k hP d rank b.toNat hr (by omega)) $$ HR Hcredit

/-- A single fair bit pays the two exact scan continuations. -/
theorem twp_round (E : CoPset) (ws : List ℕ) (k : ℕ) (hP : ws.sum ≤ 2 ^ k)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (R : IProp GF)
    (restart : R ⊢ ↯ (credit ws F + 2 * ε) -∗
      tglWp E (run ws (2 ^ k) (2 ^ k / 2) 0) (resultPost F))
    (h d : ℕ)
    (ih : ∀ rank, rank < alive ws k (d + 1) →
      R ⊢ ↯ (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1) rank) -∗
        tglWp E (expression ws k (d + 1) rank) (resultPost F))
    (rank : ℕ) (hr : rank < alive ws k d) :
    R ⊢ ↯ (DdgCredits.cutCredit (columns ws k) (extended ws F ε) (h + 1) d rank) -∗
      tglWp E (expression ws k d rank) (resultPost F) := by
  iintro HR Hcredit
  twp_pures
  twp_bind pl(rand(#2, #()))
  iapply (twp_rand_exp (ε₂ := fun b => DdgCredits.scan (columns ws k d) (2 * rank + b)
    (extended ws F ε) (DdgCredits.cutCredit (columns ws k) (extended ws F ε) h (d + 1)))
    (by decide) (KnuthYaoColumns.bit_expectation (matrix ws k) (2 ^ k)
      (extended ws F ε) h d rank).le) $$ Hcredit
  iintro %b ⟨%hb, Hcredit⟩
  simp only [Exp.ofVal]
  ieval (
    change _ ⊢ tglWp E
      (Program.afterRandClosed ws (2 ^ k) ws.sum (FldrDyadic.place k d) rank b) (resultPost F))
  iapply twp_after_bit E ws k hP F ε R restart h d ih rank hr b hb $$ HR Hcredit

end specification

end

end SampLib.FastLoadedDice
