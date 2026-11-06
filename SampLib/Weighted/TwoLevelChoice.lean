import SampLib.Weighted.Laws.WeightedBlocks
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.ClosedExp
import SampLib.Core.SupportedSpec
import Samplers.Weighted.Choice

/-! # Categorical sampling through consecutive blocks

The program groups weights, chooses a block by its total, then chooses within
that block. Only positive-mass blocks reach the second categorical call.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.TwoLevelChoice

noncomputable section

private def splitTerm {rT : Type _} : Exp rT := pl%
  rec take ys remaining :=
    if remaining = #0 then (inl(#()), ys) else case! ys
      | inl(v) => (inl(#()), inl(#()))
      | inr(q) =>
        let rest := take (snd(q)) (remaining - #1);
        (inr(((fst(q)), (fst(rest)))), (snd(rest)))

private instance split_closed {rT : Type _} : ClosedExp (splitTerm : Exp rT) where
  lc := by is_lc
  fv := by simp [splitTerm, Exp.fv]

private def groupTerm {rT : Type _} (size : ℕ) : Exp rT :=
  Exp.subst (pl% rec group xs := case! xs
    | inl(v) => inl(#())
    | inr(p) =>
      let split := splitter;
      let part := split xs #int (size : ℤ);
      inr(((fst(part)), group (snd(part))))) (.named "splitter") splitTerm

private def totalsTerm {rT : Type _} : Exp rT := pl%
  rec sumBlocks xs := case! xs
    | inl(v) => inl(#())
    | inr(p) => inr((&Occil.sumInts (fst(p)), sumBlocks (snd(p))))

private instance weighted_closed {rT : Type _} : ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Occil.uniformInt, Exp.fv]

private instance getAt_closed {rT : Type _} : ClosedExp (Occil.getAt : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.getAt, Exp.fv]

private instance sum_closed {rT : Type _} : ClosedExp (Occil.sumInts : Exp rT) where
  lc := WeightedValidation.sumInts_lc
  fv := WeightedValidation.sumInts_fv

private instance valid_closed {rT : Type _} : ClosedExp (Occil.Weighted.validWeights : Exp rT) where
  lc := WeightedValidation.validWeights_lc
  fv := WeightedValidation.validWeights_fv

private theorem positive_test (size : ℕ) (hs : 0 < size) :
    decide ((size : ℤ) ≤ 0) = false := decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_split (E : CoPset) (ws : List ℕ) (k : ℕ) :
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

private theorem twp_group (E : CoPset) (size : ℕ) [NeZero size] (ws : List ℕ) :
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

private theorem twp_totals (E : CoPset) (blocks : List (List ℕ)) :
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

private theorem twp_blockAt (E : CoPset) (blocks : List (List ℕ)) (i : ℕ)
    (hi : 0 < (WeightedBlocks.blockAt blocks i).sum) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (listVal (fun n : ℕ => Val.int n)) blocks).fst
      #int (i : ℤ))
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        (WeightedBlocks.blockAt blocks i)⌝)) := by
  have hindex := WeightedBlocks.index_lt blocks i hi
  simpa only [WeightedBlocks.blockAt, List.getElem?_eq_getElem hindex, Option.getD_some,
    List.get_eq_getElem] using
    twp_getAt E (listVal (fun n : ℕ => Val.int n)) blocks ⟨i, hindex⟩

variable [ProbLangDist.IsUniformInt rT]

/-- Conditional block sampling realizes the canonical categorical law for every positive size. -/
theorem twoLevelChoice_distSpec (E : CoPset) (ws : List ℕ) (size : ℕ)
    [NeZero ws.sum] [NeZero size] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.twoLevelChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (size : ℤ) #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int (i : ℤ)) := by
  let : NeZero (WeightedBlocks.totals (WeightedBlocks.chunks size ws)).sum := ⟨by
    rw [WeightedBlocks.sum_totals]
    exact NeZero.ne ws.sum⟩
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  twp_pures
  rw [positive_test size (NeZero.pos size)]
  twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&(groupTerm size) &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_group E size ws
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&totalsTerm &(listVal (listVal (fun n : ℕ => Val.int n))
    (WeightedBlocks.chunks size ws)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_totals E (WeightedBlocks.chunks size ws)
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n)
    (WeightedBlocks.totals (WeightedBlocks.chunks size ws))).fst)
  isimp only [← WeightedBlocks.expectation size ws F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E
    (WeightedBlocks.totals (WeightedBlocks.chunks size ws))).wp_supported
    (fun i => 0 < (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i).sum)
    (Set.to_countable _).measurableSet (WeightedBlocks.ae_pos_block _)
    (WeightedBlocks.continuation size (WeightedBlocks.chunks size ws) F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  let : NeZero (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i).sum := ⟨hi.ne'⟩
  twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&Occil.getAt &(listVal (listVal (fun n : ℕ => Val.int n))
    (WeightedBlocks.chunks size ws)).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_blockAt E (WeightedBlocks.chunks size ws) i hi
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n)
    (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i)).fst)
  isimp only [WeightedBlocks.continuation] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E
    (WeightedBlocks.blockAt (WeightedBlocks.chunks size ws) i)).wp
    (fun j => F (i * size + j)) (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  twp_pures
  twp_value
  imodintro
  iexists i * size + j
  iframe Hcredit
  ipureintro
  exact Val.ext (by simp only [Nat.cast_add, Nat.cast_mul])

end specification

end

end SampLib.TwoLevelChoice
