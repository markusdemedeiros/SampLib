import SampLib.ListEncoding
import Samplers.Combinatorial.Basic

/-! # Consecutive integer lists -/

open ProbLang

namespace SampLib.IntegerRange

def interval (lo : ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => lo :: interval (lo + 1) n

theorem intRange_lc {rT : Type _} :
    (Occil.intRange : Exp rT).IsLocallyClosed := by is_lc

theorem intRange_fv {rT : Type _} : (Occil.intRange : Exp rT).fv = ∅ := by
  simp [Occil.intRange, Exp.fv]

@[simp] theorem intRange_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.intRange = Occil.intRange :=
  (Exp.open_lc k e _ intRange_lc).symm

@[simp] theorem intRange_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.intRange : Exp rT) = Occil.intRange :=
  Exp.closeRec_fresh x _ k (by simp [intRange_fv])

private theorem empty_test (lo : ℤ) : decide (lo + ((0 : ℕ) : ℤ) ≤ lo) = true := by
  simp

private theorem range_test (lo : ℤ) (n : ℕ) :
    decide (lo + ((n + 1 : ℕ) : ℤ) ≤ lo) = false := by
  apply decide_eq_false
  omega

private theorem endpoint (lo : ℤ) (n : ℕ) :
    lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + n := by push_cast; ring

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℤ) (xs : List ℤ) :
    pl(inr((#int x, {Exp.ofVal (listVal Val.int xs)}))) =
      Exp.ofVal (listVal Val.int (x :: xs) : Val rT) := by simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The deterministic range constructor enumerates its half-open integer interval. -/
theorem twp_intRange (E : CoPset) (lo : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.intRange #int lo #int (lo + (n : ℤ)))
      (fun v : Val rT => iprop(⌜v = listVal Val.int (interval lo n)⌝)) := by
  induction n generalizing lo with
  | zero =>
    twp_pures
    rw [empty_test]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    twp_pures
    rw [range_test]
    twp_pure
    twp_pure
    rw [endpoint]
    twp_bind pl(&Occil.intRange #int (lo + 1) #int ((lo + 1) + (n : ℤ)))
    iapply tglWp_wand
    isplitl []
    · iapply IH (lo + 1)
    iintro %v %hv
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int (lo :: interval (lo + 1) n)))
    ipureintro
    rfl

end specification

end SampLib.IntegerRange
