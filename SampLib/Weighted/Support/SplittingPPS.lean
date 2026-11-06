import SampLib.Weighted.Laws.SplittingPPSRecursion
import SampLib.Common.WeightedValidation
import SampLib.Weighted.Syntax.SplittingPPS
import Samplers.Weighted.Reservoir

/-! # Deterministic preprocessing for Deville–Tillé splitting -/

open ProbLang

namespace SampLib.SplittingPPS

/-- Source representation of an inclusion numerator and its original label. -/
abbrev itemVal {rT : Type} (a : Item) : Val rT := .pair (.int a.1) (.int a.2)

private theorem order_test (a b : Item) :
    decide ((a.1 : ℤ) ≤ b.1) = decide (ordered a b) := by
  apply decide_eq_decide.mpr
  change (a.1 : ℤ) ≤ b.1 ↔ a.1 ≤ b.1
  omega

private theorem capacity_test (count total w : ℕ) (h : count * w ≤ total) :
    decide ((total : ℤ) < (count : ℤ) * w) = false :=
  decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem multiplication_cast (count w : ℕ) :
    (count : ℤ) * w = ((count * w : ℕ) : ℤ) := by norm_cast

private theorem successor_test (n : ℕ) :
    decide ((0 : ℤ) < (n + 1 : ℕ)) = true := decide_eq_true (by omega)

private theorem subtraction_cast (w amount : ℕ) (h : amount ≤ w) :
    (w : ℤ) - amount = ((w - amount : ℕ) : ℤ) := (Nat.cast_sub h).symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] insert_openRec insert_closeRec

/-- Source insertion agrees with stable insertion by the inclusion numerator. -/
theorem twp_insertProbability (E : CoPset) (item : Item) (items : List Item) :
    ⊢ tglWp E pl(&Occil.Weighted.insertProbability &(itemVal item).fst
        &(listVal itemVal items).fst)
      (fun v => iprop(⌜v = listVal itemVal (items.orderedInsert ordered item)⌝)) := by
  induction items with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [List.orderedInsert_nil]
    exact Val.ext rfl
  | cons first items ih =>
    simp only [listVal, itemVal]
    twp_pures
    rw [order_test item first]
    by_cases h : ordered item first
    · rw [decide_eq_true h]
      twp_pures
      let result : Val rT := .inr (.pair (itemVal item)
        (.inr (.pair (itemVal first) (listVal itemVal items))))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      rw [List.orderedInsert_cons, ite_eq_left h]
      exact Val.ext rfl
    · rw [decide_eq_false h]
      iterate 2 twp_pure
      twp_bind pl(&Occil.Weighted.insertProbability &(itemVal item).fst
        &(listVal itemVal items).fst)
      iapply tglWp_wand
      isplitl []
      · iapply ih
      iintro %v %hv
      subst v
      simp only [Exp.ofVal]
      let result : Val rT := .inr (.pair (itemVal first)
        (listVal itemVal (items.orderedInsert ordered item)))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      rw [List.orderedInsert_cons, ite_eq_right h]
      exact Val.ext rfl

/-- Source preprocessing constructs the exact stable ordering of scaled input weights. -/
theorem twp_prepare (E : CoPset) (count total : ℕ) (ws : List ℕ) (label : ℤ)
    (hcap : ∀ w ∈ ws, count * w ≤ total) :
    ⊢ tglWp E pl(&(Program.prepare (count : ℤ) (total : ℤ))
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int label)
      (fun v => iprop(⌜v = listVal itemVal (prepare count ws label)⌝)) := by
  induction ws generalizing label with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [prepare_nil]
    exact Val.ext rfl
  | cons w ws ih =>
    have hw := hcap w (by simp)
    have htail : ∀ a ∈ ws, count * a ≤ total := fun a ha => hcap a (by simp [ha])
    simp only [listVal]
    twp_pures
    rw [capacity_test count total w hw]
    rw [multiplication_cast count w]
    iterate 3 twp_pure
    twp_bind pl(&(Program.prepare (count : ℤ) (total : ℤ))
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (label + 1))
    iapply tglWp_wand
    isplitl []
    · iapply ih (label + 1) htail
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.Weighted.insertProbability &(itemVal (count * w, label)).fst
      &(listVal itemVal (prepare count ws (label + 1))).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_insertProbability E (count * w, label) (prepare count ws (label + 1))
    iintro %v %hv
    subst v
    iapply (tglWp_value (v := listVal itemVal
      ((prepare count ws (label + 1)).orderedInsert ordered (count * w, label))))
    ipureintro
    rw [prepare_cons]

private theorem twp_adjust_finish (E : CoPset) (amount : ℕ) (remaining : ℤ)
    (item : Item) (numerator : ℕ) (items : List Item)
    (hrec : ⊢ tglWp E pl(&(Program.adjust (amount : ℤ)) &(listVal itemVal items).fst
      #int remaining) (fun v => iprop(⌜v = listVal itemVal
        (adjust amount remaining.toNat items)⌝))) :
    ⊢ tglWp E (Program.finish amount remaining item.1 item.2 numerator (listVal itemVal items))
      (fun v => iprop(⌜v = listVal itemVal
        ((adjust amount remaining.toNat items).orderedInsert ordered (numerator, item.2))⌝)) := by
  twp_bind pl(&(Program.adjust (amount : ℤ)) &(listVal itemVal items).fst #int remaining)
  iapply tglWp_wand
  isplitl []
  · iapply hrec
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.insertProbability &(itemVal (numerator, item.2)).fst
    &(listVal itemVal (adjust amount remaining.toNat items)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_insertProbability E (numerator, item.2) (adjust amount remaining.toNat items)
  iintro %v %hv
  subst v
  iapply (tglWp_value (v := listVal itemVal
    ((adjust amount remaining.toNat items).orderedInsert ordered (numerator, item.2))))
  itrivial

/-- Subtraction and stable reinsertion implement the exact residual update. -/
theorem twp_adjust (E : CoPset) (amount : ℕ) (remaining : ℤ) (items : List Item)
    (htop : ∀ a ∈ items.drop remaining.toNat, amount ≤ a.1) :
    ⊢ tglWp E pl(&(Program.adjust (amount : ℤ)) &(listVal itemVal items).fst #int remaining)
      (fun v => iprop(⌜v = listVal itemVal (adjust amount remaining.toNat items)⌝)) := by
  induction items generalizing remaining with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [adjust_nil]
    exact Val.ext rfl
  | cons item items ih =>
    have htail := drop_tail_condition amount remaining item items htop
    have hrec := ih (remaining - 1) htail
    simp only [listVal, itemVal]
    iterate 8 twp_pure
    by_cases hp : 0 < remaining
    · rw [decide_eq_true hp]
      iterate 5 twp_pure
      isimp only [adjust_cons_int, ite_eq_left hp, Exp.ofVal]
      iapply twp_adjust_finish E amount (remaining - 1) item item.1 items hrec
    · rw [decide_eq_false hp]
      iterate 6 twp_pure
      rw [subtraction_cast item.1 amount (upper_head_bound amount remaining item items hp htop)]
      isimp only [adjust_cons_int, ite_eq_right hp, Exp.ofVal]
      iapply twp_adjust_finish E amount (remaining - 1) item (item.1 - amount) items hrec

/-- The accepting branch drops the lower block and returns the upper labels in source order. -/
theorem twp_select (E : CoPset) (items : List Item) (remaining : ℕ) :
    ⊢ tglWp E pl(&Program.select &(listVal itemVal items).fst #int (remaining : ℤ))
      (fun v => iprop(⌜v = listVal Val.int ((items.drop remaining).map Prod.snd)⌝)) := by
  induction items generalizing remaining with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [List.drop_nil, List.map_nil, listVal]
  | cons first items ih =>
    cases remaining with
    | zero =>
      simp only [listVal, itemVal]
      iterate 10 twp_pure
      twp_bind pl(&Program.select &(listVal itemVal items).fst #int (0 : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply ih 0
      iintro %v %hv
      subst v
      twp_pures
      simp only [Exp.ofVal, List.drop_zero]
      let result : Val rT := .inr (.pair (.int first.2) (listVal Val.int (items.map Prod.snd)))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      simp only [List.map_cons, listVal]
      rfl
    | succ remaining =>
      simp only [listVal, itemVal]
      iterate 8 twp_pure
      rw [successor_test remaining]
      iterate 3 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Program.select &(listVal itemVal items).fst #int (remaining : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply ih remaining
      iintro %v %hv
      subst v
      iapply (tglWp_value (v := listVal Val.int ((items.drop remaining).map Prod.snd)))
      ipureintro
      simp only [List.drop_succ_cons]

end specification

end SampLib.SplittingPPS
