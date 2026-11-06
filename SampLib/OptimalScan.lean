import SampLib.Syntax.Optimal
import SampLib.DdgScan

/-! # The actual finite cyclic matrix's ordered column scan -/

open ProbLang

namespace SampLib.OptimalScan

/-- A leaf index or the remaining live rank, in the source's bool/pair representation. -/
def encode {rT : Type} (offset : ℕ) : ℕ ⊕ ℕ → Val rT
  | .inl i => Val.pair (Val.bool true) (Val.int ((offset + i : ℕ) : ℤ))
  | .inr r => Val.pair (Val.bool false) (Val.int (r : ℤ))

def digit (m position : ℕ) : ℕ := m / 2 ^ position % 2

private theorem shift_encode {rT : Type} (offset : ℕ) (r : ℕ ⊕ ℕ) :
    (encode (offset + 1) r : Val rT) = encode offset (r.map Nat.succ id) := by
  cases r with
  | inl i => simp [encode, add_comm, add_left_comm]
  | inr r => rfl

private theorem digit_cast (m position : ℕ) :
    ((m : ℤ) / (2 : ℤ) ^ position) % 2 = (digit m position : ℤ) := by
  norm_cast

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The original scan consumes binary leaves in row order and returns the untouched live rank. -/
theorem twp_scan (E : CoPset) (rows : List ℕ) (position d offset : ℕ) :
    ⊢ tglWp E pl(&(Optimal.Program.scan : Exp rT)
      &(listVal (fun m : ℕ => Val.int m) rows).fst
      #int (d : ℤ) #int (position : ℤ) #int (offset : ℤ))
      (fun v : Val rT => iprop(⌜v = encode offset
        (DdgScan.result (rows.map (fun m => digit m position)) d)⌝)) := by
  induction rows generalizing d offset with
  | nil =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons m rows ih =>
    iterate 7 twp_pure
    twp_bind pl(&Occil.Weighted.integerPower #2 #int (position : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply WeightedIntegerPower.twp_integerPower E 2 position
    iintro %v %hv
    subst v
    twp_pures
    rw [digit_cast]
    by_cases h : d < digit m position
    · rw [decide_eq_true (show (d : ℤ) - digit m position < 0 by omega)]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp only [List.map_cons, DdgScan.result, h, ite_true, encode, add_zero]
    · rw [decide_eq_false
        (show ¬(d : ℤ) - digit m position < 0 by omega)]
      iterate 3 twp_pure
      have hd : digit m position ≤ d := Nat.le_of_not_lt h
      rw [← Nat.cast_sub hd,
        show (offset : ℤ) + 1 = ((offset + 1 : ℕ) : ℤ) by norm_cast]
      have hrec := ih (d - digit m position) (offset + 1)
      simp only [shift_encode] at hrec
      simp only [List.map_cons, DdgScan.result, h, ite_false]
      ieval (
        change _ ⊢ tglWp E pl(&(Optimal.Program.scan : Exp rT)
          &(listVal (fun m : ℕ => Val.int m) rows).fst
          #int ((d - digit m position : ℕ) : ℤ) #int (position : ℤ)
          #int ((offset + 1 : ℕ) : ℤ)) _)
      iapply hrec

end specification

end SampLib.OptimalScan
