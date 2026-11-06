import SampLib.Distributions.HanHoshiHorizon
import SampLib.Syntax.HanHoshi

/-! # Deterministic cumulative-cell scanning for Han–Hoshi -/

open ProbLang

namespace SampLib.HanHoshi

/-- The source's failure sentinel and original-position labels. -/
def scanResult (label : ℤ) : Option ℕ → ℤ
  | none => -1
  | some i => label + i

private theorem fits_test (total value denominator before w : ℕ) :
    Bool.and (decide ((before : ℤ) * denominator ≤ (value : ℤ) * total))
      (decide (((value : ℤ) + 1) * total ≤ ((before : ℤ) + w) * denominator)) =
        decide (Fits total value denominator before (before + w)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold Fits
  norm_cast

private theorem scanResult_tail (label : ℤ) (r : Option ℕ) :
    scanResult (label + 1) r = scanResult label (r.map Nat.succ) := by
  cases r with
  | none => rfl
  | some i => simp [scanResult, Nat.cast_add, add_comm, add_left_comm]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.HanHoshi.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The deterministic source scan reports exactly the first whole-cell certificate. -/
theorem twp_find (E : CoPset) (total value denominator : ℕ) (ws : List ℕ)
    (before : ℕ) (label : ℤ) :
    ⊢ tglWp E pl(&(Program.find (total : ℤ))
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (before : ℤ) #int (value : ℤ)
      #int (denominator : ℤ) #int label)
      (fun v : Val rT => iprop(⌜v = Val.int
        (scanResult label (scan total value denominator ws before))⌝)) := by
  induction ws generalizing before label with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [scan, scanResult]
  | cons w ws ih =>
    simp only [listVal]
    twp_pures
    rw [fits_test]
    by_cases hf : Fits total value denominator before (before + w)
    · rw [decide_eq_true hf]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp only [scan, ite_eq_left hf, scanResult, Nat.cast_zero, add_zero]
    · rw [decide_eq_false hf]
      iterate 3 twp_pure
      rw [← Nat.cast_add before w]
      twp_bind pl(&(Program.find (total : ℤ))
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int ((before + w : ℕ) : ℤ)
        #int (value : ℤ) #int (denominator : ℤ) #int (label + 1))
      iapply tglWp_wand
      isplitl []
      · iapply ih (before + w) (label + 1)
      iintro %v %hv
      subst v
      iapply (tglWp_value (v := Val.int
        (scanResult (label + 1) (scan total value denominator ws (before + w)))))
      ipureintro
      rw [scan, ite_eq_right hf, scanResult_tail]

end specification

end SampLib.HanHoshi
