import SampLib.Weighted.Laws.WeightedBlocks
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.ClosedExp
import Samplers.Weighted.Choice

/-! # Grouping weights into blocks and their totals

Deterministic helpers for two-level categorical sampling: split a weight list into
consecutive blocks, sum each block, and look up one block.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.TwoLevelChoice

noncomputable section

def splitTerm {rT : Type _} : Exp rT := pl%
  rec take ys remaining :=
    if remaining = #0 then (inl(#()), ys) else case! ys
      | inl(v) => (inl(#()), inl(#()))
      | inr(q) =>
        let rest := take (snd(q)) (remaining - #1);
        (inr(((fst(q)), (fst(rest)))), (snd(rest)))

instance split_closed {rT : Type _} : ClosedExp (splitTerm : Exp rT) where
  lc := by is_lc
  fv := by simp [splitTerm, Exp.fv]

def groupTerm {rT : Type _} (size : ℕ) : Exp rT :=
  Exp.subst (pl% rec group xs := case! xs
    | inl(v) => inl(#())
    | inr(p) =>
      let split := splitter;
      let part := split xs #int (size : ℤ);
      inr(((fst(part)), group (snd(part))))) (.named "splitter") splitTerm

def totalsTerm {rT : Type _} : Exp rT := pl%
  rec sumBlocks xs := case! xs
    | inl(v) => inl(#())
    | inr(p) => inr((&Occil.sumInts (fst(p)), sumBlocks (snd(p))))

instance weighted_closed {rT : Type _} : ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Occil.uniformInt, Exp.fv]

instance getAt_closed {rT : Type _} : ClosedExp (Occil.getAt : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.getAt, Exp.fv]

instance sum_closed {rT : Type _} : ClosedExp (Occil.sumInts : Exp rT) where
  lc := WeightedValidation.sumInts_lc
  fv := WeightedValidation.sumInts_fv

instance valid_closed {rT : Type _} : ClosedExp (Occil.Weighted.validWeights : Exp rT) where
  lc := WeightedValidation.validWeights_lc
  fv := WeightedValidation.validWeights_fv

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_split (E : CoPset) (ws : List ℕ) (k : ℕ) :
    ⊢ tglWp E pl(&splitTerm &(listVal (fun n : ℕ => Val.int n) ws).fst #int (k : ℤ))
      (fun v => iprop(⌜v = Val.pair (listVal (fun n : ℕ => Val.int n) (ws.take k))
        (listVal (fun n : ℕ => Val.int n) (ws.drop k))⌝)) := by
  induction k generalizing ws with
  | zero =>
    twp_pures
    let result : Val rT := .pair (.inl .unit) (listVal (fun n : ℕ => Val.int n) ws)
    iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
    ipureintro
    exact Val.ext rfl
  | succ k ih =>
    cases ws with
    | nil =>
      simp only [listVal]
      twp_pures
      twp_value
      imodintro
      ipureintro
      exact Val.ext rfl
    | cons w ws =>
      simp only [listVal]
      iterate 9 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&splitTerm &(listVal (fun n : ℕ => Val.int n) ws).fst #int (k : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply ih ws
      iintro %v %hv
      subst v
      twp_pures
      simp only [Exp.ofVal]
      let result : Val rT := .pair
        (.inr (.pair (.int (w : ℤ)) (listVal (fun n : ℕ => Val.int n) (ws.take k))))
        (listVal (fun n : ℕ => Val.int n) (ws.drop k))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      exact Val.ext rfl

theorem twp_group (E : CoPset) (size : ℕ) [NeZero size] (ws : List ℕ) :
    ⊢ tglWp E pl(&(groupTerm size) &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v => iprop(⌜v = listVal (listVal (fun n : ℕ => Val.int n))
        (WeightedBlocks.chunks size ws)⌝)) := by
  induction ws using (measure (fun xs : List ℕ => xs.length)).wf.induction with
  | h xs ih =>
    cases xs with
    | nil =>
      simp [groupTerm, Exp.subst, Exp.close, Exp.closeRec, listVal]
      twp_pures
      twp_value
      imodintro
      ipureintro
      exact Val.ext rfl
    | cons w ws =>
      simp [groupTerm, Exp.subst, Exp.close, Exp.closeRec, listVal]
      iterate 5 twp_pure
      simp only [ClosedExp.openRec]
      twp_bind pl(&splitTerm &(listVal (fun n : ℕ => Val.int n) (w :: ws)).fst
        #int (size : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply twp_split E (w :: ws) size
      iintro %v %hv
      subst v
      iterate 2 twp_pure
      simp only [ClosedExp.openRec]
      twp_bind pl(&(groupTerm size)
        &(listVal (fun n : ℕ => Val.int n) ((w :: ws).drop size)).fst)
      iapply tglWp_wand
      isplitl []
      · iapply ih _ (WeightedBlocks.drop_length_lt size w ws)
      iintro %v %hv
      subst v
      twp_pures
      simp only [Exp.ofVal]
      let result : Val rT := .inr (.pair
        (listVal (fun n : ℕ => Val.int n) ((w :: ws).take size))
        (listVal (listVal (fun n : ℕ => Val.int n))
          (WeightedBlocks.chunks size ((w :: ws).drop size))))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      rw [WeightedBlocks.chunks_cons]
      exact Val.ext rfl

theorem twp_totals (E : CoPset) (blocks : List (List ℕ)) :
    ⊢ tglWp E pl(&totalsTerm &(listVal (listVal (fun n : ℕ => Val.int n)) blocks).fst)
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n) (WeightedBlocks.totals blocks)⌝)) := by
  induction blocks with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons block blocks ih =>
    simp only [listVal]
    iterate 5 twp_pure
    twp_bind pl(&totalsTerm &(listVal (listVal (fun n : ℕ => Val.int n)) blocks).fst)
    iapply tglWp_wand
    isplitl []
    · iapply ih
    iintro %v %hv
    subst v
    twp_pure
    simp only [WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec]
    twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) block).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E block
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    let result : Val rT := .inr (.pair (.int (block.sum : ℤ))
      (listVal (fun n : ℕ => Val.int n) (WeightedBlocks.totals blocks)))
    iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
    ipureintro
    exact Val.ext rfl

theorem twp_blockAt (E : CoPset) (blocks : List (List ℕ)) (i : ℕ)
    (hi : 0 < (WeightedBlocks.blockAt blocks i).sum) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (listVal (fun n : ℕ => Val.int n)) blocks).fst
      #int (i : ℤ))
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        (WeightedBlocks.blockAt blocks i)⌝)) := by
  have hindex := WeightedBlocks.index_lt blocks i hi
  simpa only [WeightedBlocks.blockAt, List.getElem?_eq_getElem hindex, Option.getD_some,
    List.get_eq_getElem] using
    twp_getAt E (listVal (fun n : ℕ => Val.int n)) blocks ⟨i, hindex⟩

end specification

end

end SampLib.TwoLevelChoice
