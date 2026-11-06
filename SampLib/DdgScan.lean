import SampLib.Distributions.DdgCredits
import SampLib.ListEncoding
import Samplers.Weighted.Trees

/-! # The actual Knuth–Yao column scanner -/

open ProbLang
open scoped ENNReal

namespace SampLib.DdgScan

noncomputable section

/-- A leaf label or the distance left after all column leaves have been consumed. -/
def result : List ℕ → ℕ → ℕ ⊕ ℕ
  | [], d => .inr d
  | b :: bs, d => if d < b then .inl 0 else (result bs (d - b)).map Nat.succ id

theorem result_bounds (bs : List ℕ) (d : ℕ) :
    match result bs d with
    | .inl i => i < bs.length
    | .inr r => bs.sum + r = d := by
  induction bs generalizing d with
  | nil => simp [result]
  | cons b bs ih =>
    by_cases h : d < b
    · simp [result, h]
    · have hi := ih (d - b)
      cases hr : result bs (d - b) with
      | inl i =>
        simp only [hr] at hi
        simpa [result, h, hr] using Nat.succ_lt_succ hi
      | inr r =>
        simp only [hr] at hi
        simp only [result, h, ite_false, hr, Sum.map_inr, id_eq, List.sum_cons]
        omega

theorem scan_eq (bs : List ℕ) (d : ℕ) (F next : ℕ → ℝ≥0∞) :
    DdgCredits.scan bs d F next =
      match result bs d with
      | .inl i => F i
      | .inr r => next r := by
  induction bs generalizing d F with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : d < b
    · simp only [DdgCredits.scan, result, h, ite_true]
    · simp only [DdgCredits.scan, result, h, ite_false]
      rw [ih]
      cases result bs (d - b) <;> rfl

/-- The source computes a binary digit of the exact rational weight. -/
def digit (w multiplier denominator : ℕ) : ℕ := (w * multiplier / denominator) % 2

def encode {rT : Type} (offset : ℕ) : ℕ ⊕ ℕ → Val rT
  | .inl i => Val.inl (Val.int ((offset + i : ℕ) : ℤ))
  | .inr r => Val.inr (Val.int (r : ℤ))

private theorem digit_cast (w multiplier denominator : ℕ) :
    (((w : ℤ) * multiplier / denominator) % 2) = (digit w multiplier denominator : ℤ) := by
  simp only [digit, Int.natCast_emod, Int.natCast_ediv, Int.natCast_mul, Nat.cast_ofNat]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Deterministic symbolic execution of the original, on-the-fly rational column scan. -/
theorem twp_matrixColumn (E : CoPset) (ws : List ℕ) (multiplier denominator d offset : ℕ) :
    ⊢ tglWp E pl(&Occil.Weighted.matrixColumn
      &(listVal (fun w : ℕ => Val.int w) ws).fst
      #int (multiplier : ℤ) #int (denominator : ℤ) #int (d : ℤ) #int (offset : ℤ))
      (fun v : Val rT => iprop(⌜v = encode offset
        (result (ws.map (fun w => digit w multiplier denominator)) d)⌝)) := by
  induction ws generalizing d offset with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons w ws ih =>
    simp only [listVal]
    twp_pures
    rw [digit_cast]
    simp only [Int.ofNat_lt]
    by_cases h : d < digit w multiplier denominator
    · rw [decide_eq_true h]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp [result, h, encode]
    · rw [decide_eq_false h]
      iterate 4 twp_pure
      rw [← Nat.cast_sub (Nat.le_of_not_gt h), ← Nat.cast_add_one]
      simp only [Exp.ofVal]
      ieval (
        change _ ⊢ tglWp E pl(&Occil.Weighted.matrixColumn
          &(listVal (fun w : ℕ => Val.int w) ws).fst
          #int (multiplier : ℤ) #int (denominator : ℤ)
          #int ((d - digit w multiplier denominator : ℕ) : ℤ)
          #int ((offset + 1 : ℕ) : ℤ)) _)
      iapply tglWp_wand
      isplitl []
      · iapply ih (d - digit w multiplier denominator) (offset + 1)
      iintro %v %hv
      ipureintro
      simp only [List.map_cons, result, h, ite_false]
      have he (r : ℕ ⊕ ℕ) : encode (rT := rT) offset (r.map Nat.succ id) =
          encode (offset + 1) r := by
        cases r with
        | inl i =>
          apply Val.ext
          simp [encode, add_comm, add_left_comm]
        | inr r => rfl
      rw [he]
      exact hv

end specification

end

end SampLib.DdgScan
