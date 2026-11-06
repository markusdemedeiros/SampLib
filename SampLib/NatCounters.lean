import SampLib.ListEncoding
import Samplers.Discrete.Combinatorics
import Samplers.Discrete.Urns

/-! Deterministic natural-number counters used by multivariate samplers. -/

open ProbLang

namespace SampLib.NatCounters

abbrev encode {rT : Type _} [ProbLangℝ rT] (xs : List ℕ) : Val rT :=
  listVal (fun n : ℕ => Val.int (n : ℤ)) xs

private theorem cons_value {rT : Type _} [ProbLangℝ rT] (x : ℕ) (xs : List ℕ) :
    (pl(inr((#int (x : ℤ), {Exp.ofVal (encode xs)}))) : Exp rT) =
      Exp.ofVal (encode (x :: xs)) := by
  simp [encode, listVal, Exp.ofVal]

private theorem zero_cons_value {rT : Type _} [ProbLangℝ rT] (xs : List ℕ) :
    (pl(inr((#0, {Exp.ofVal (encode xs)}))) : Exp rT) =
      Exp.ofVal (encode (0 :: xs)) := by
  simpa only [Nat.cast_zero] using cons_value (rT := rT) 0 xs

private theorem decrement_coe (x : ℕ) (hx : 0 < x) :
    (x : ℤ) + -1 = ((x - 1 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Build a list of zero counters, including the empty list. -/
theorem twp_zeroCounters (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.zeroCounters #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (List.replicate n 0)⌝)) := by
  induction n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | succ n IH =>
    iterate 5 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.DiscreteExtra.zeroCounters #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    rw [zero_cons_value]
    iapply (tglWp_value (v := encode (0 :: List.replicate n 0)))
    ipureintro
    simp only [List.replicate_succ]

/-- Increment exactly the indexed counter. -/
theorem twp_incrementCounter (E : CoPset) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.incrementCounter &(encode xs).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (xs.modify i (· + 1))⌝)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs IH =>
    cases i with
    | zero =>
      simp only [encode, listVal, List.modify_zero_cons]
      twp_pures
      rw [← Nat.cast_add_one, cons_value]
      iapply (tglWp_value (v := encode ((x + 1) :: xs)))
      ipureintro
      rfl
    | succ i =>
      simp only [encode, listVal, List.modify_succ_cons]
      iterate 9 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.DiscreteExtra.incrementCounter &(encode xs).fst #int (i : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply IH i (by simpa using hi)
      iintro %v %hv
      subst v
      twp_pures
      rw [cons_value]
      iapply (tglWp_value (v := encode (x :: xs.modify i (· + 1))))
      ipureintro
      rfl

/-- Decrement an in-range positive counter, preserving the natural encoding. -/
theorem twp_decrementCounter (E : CoPset) (xs : List ℕ) (i : ℕ) (hi : i < xs.length)
    (hpos : 0 < xs[i]) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.adjustCounter &(encode xs).fst
      #int (i : ℤ) #int (-1 : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (xs.modify i (· - 1))⌝)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs IH =>
    cases i with
    | zero =>
      have hx : 0 < x := by simpa using hpos
      simp only [encode, listVal, List.modify_zero_cons]
      twp_pures
      rw [decrement_coe x hx, cons_value]
      iapply (tglWp_value (v := encode ((x - 1) :: xs)))
      ipureintro
      rfl
    | succ i =>
      simp only [encode, listVal, List.modify_succ_cons]
      iterate 10 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.DiscreteExtra.adjustCounter &(encode xs).fst
        #int (i : ℤ) #int (-1 : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply IH i (by simpa using hi) (by simpa using hpos)
      iintro %v %hv
      subst v
      twp_pure
      rw [cons_value]
      iapply (tglWp_value (v := encode (x :: xs.modify i (· - 1))))
      ipureintro
      rfl

end specification

end SampLib.NatCounters
