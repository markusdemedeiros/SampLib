import SampLib.Weighted.Laws.FastLoadedDiceScan
import SampLib.Weighted.Syntax.FastLoadedDice

/-! # Symbolic execution of FLDR's real rows and implicit rejection row -/

open ProbLang
open scoped ENNReal

namespace SampLib.FastLoadedDice

noncomputable section

open Program FastLoadedDiceCredits FastLoadedDiceScan

@[pl_fold] def run {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (P place rank : ℕ) : Exp rT :=
  pl(&(loop ws P ws.sum) #int (place : ℤ) #int (rank : ℤ))

private theorem digit_cast (w place : ℕ) :
    ((w : ℤ) / place % 2) = ((w / place % 2 : ℕ) : ℤ) := by
  simp only [Int.natCast_emod, Int.natCast_ediv, Nat.cast_ofNat]

private theorem dummy_cast (P T place : ℕ) (hP : T ≤ P) :
    (((P : ℤ) - T) / place % 2) = (dummy P T place : ℤ) := by
  simp only [dummy, Int.natCast_emod, Int.natCast_ediv, Nat.cast_sub hP, Nat.cast_ofNat]

private theorem half_cast (place : ℕ) :
    (place : ℤ) / 2 = ((place / 2 : ℕ) : ℤ) := by simp only [Int.natCast_ediv, Nat.cast_ofNat]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def resultPost (F : ℕ → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec

/-- Each real leaf returns its credit; the final implicit leaf spends the caller's restart rule. -/
theorem twp_scan (E : CoPset) (ws : List ℕ) (P place : ℕ) (hP : ws.sum ≤ P)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (next : ℕ → ℝ≥0∞) (a : ℕ) (R : IProp GF)
    (restart : R ⊢ ↯ (credit ws F + 2 * ε) -∗ tglWp E (run ws P (P / 2) 0) (resultPost F))
    (advance : ∀ r, r < a → R ⊢ ↯ (next r) -∗
      tglWp E (run ws P (place / 2) r) (resultPost F))
    (xs : List ℕ) (d offset : ℕ) (hlen : offset + xs.length = ws.length)
    (hr : d < (bits xs place ++ [dummy P ws.sum place]).sum + a) :
    R ⊢ ↯ (kernel ws P place F ε next xs d offset) -∗
      tglWp E pl(&(scan ws P ws.sum place)
        &(listVal (fun w : ℕ => Val.int w) xs).fst #int (d : ℤ) #int (offset : ℤ))
        (resultPost F) := by
  induction xs generalizing d offset with
  | nil =>
    have ho : offset = ws.length := by simpa using hlen
    subst offset
    iintro HR Hcredit
    isimp only [kernel_nil] at Hcredit
    simp only [listVal]
    twp_pures
    rw [dummy_cast P ws.sum place hP]
    simp only [Int.ofNat_lt]
    by_cases h : d < dummy P ws.sum place
    · rw [decide_eq_true h]
      isimp only [ite_eq_left h] at Hcredit
      iterate 2 twp_pure
      rw [half_cast]
      simp only [Exp.ofVal]
      ieval (change _ ⊢ tglWp E (run ws P (P / 2) 0) (resultPost F))
      iapply restart $$ HR Hcredit
    · rw [decide_eq_false h]
      isimp only [ite_eq_right h] at Hcredit
      iterate 3 twp_pure
      rw [← Nat.cast_sub (Nat.le_of_not_gt h), half_cast]
      simp only [Exp.ofVal]
      ieval (
        change _ ⊢ tglWp E (run ws P (place / 2) (d - dummy P ws.sum place)) (resultPost F))
      have hr₀ : d < dummy P ws.sum place + a := by simpa [bits] using hr
      have hb : d - dummy P ws.sum place < a := by omega
      iapply advance (d - dummy P ws.sum place) hb $$ HR Hcredit
  | cons w xs ih =>
    iintro HR Hcredit
    isimp only [kernel_cons] at Hcredit
    simp only [listVal]
    twp_pures
    rw [digit_cast]
    simp only [Int.ofNat_lt]
    by_cases h : d < w / place % 2
    · rw [decide_eq_true h]
      isimp only [ite_eq_left h] at Hcredit
      have ho : offset < ws.length := by simp only [List.length_cons] at hlen; omega
      isimp only [extended, ite_eq_left ho] at Hcredit
      twp_pures
      twp_value
      imodintro
      isimp only [resultPost]
      iexists offset
      iframe Hcredit
      itrivial
    · rw [decide_eq_false h]
      isimp only [ite_eq_right h] at Hcredit
      iterate 4 twp_pure
      rw [← Nat.cast_sub (Nat.le_of_not_gt h), ← Nat.cast_add_one]
      simp only [Exp.ofVal]
      ieval (
        change _ ⊢ tglWp E pl(&(scan ws P ws.sum place)
          &(listVal (fun w : ℕ => Val.int w) xs).fst
          #int ((d - w / place % 2 : ℕ) : ℤ) #int ((offset + 1 : ℕ) : ℤ)) (resultPost F))
      have hlen' : offset + 1 + xs.length = ws.length := by
        simp only [List.length_cons] at hlen
        omega
      have hr' : d - w / place % 2 <
          (bits xs place ++ [dummy P ws.sum place]).sum + a := by
        simp only [bits, List.map_cons, List.cons_append, List.sum_cons] at hr ⊢
        omega
      iapply ih (d - w / place % 2) (offset + 1) hlen' hr' $$ HR Hcredit

end specification

end

end SampLib.FastLoadedDice
