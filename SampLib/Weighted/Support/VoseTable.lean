import SampLib.Weighted.Support.AliasTable
import SampLib.Core.ArrayVector
import SampLib.Weighted.Laws.VoseBalance
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.Arrays

/-! # Constructing owned Vose alias tables -/

open ProbLang

namespace SampLib.VoseTable

noncomputable section

private def setup {rT : Type _} (n total : ℕ) (work aliases small large : Loc) : Exp rT := pl%
  rec fill xs index := case! xs
    | inl(v) => #()
    | inr(p) =>
      let mass := #int (n : ℤ) * fst(p);
      (#loc work +ₗ index) ← mass;
      (#loc aliases +ₗ index) ← index;
      (if mass < #int (total : ℤ) then #loc small ← inr((index, !#loc small))
        else #loc large ← inr((index, !#loc large)));
      fill (snd(p)) (index + #1)

private def balance {rT : Type _} (total : ℕ)
    (work probability aliases small large : Loc) : Exp rT := pl%
  rec prepare u := case! !#loc small
    | inl(v) => #()
    | inr(s) => case! !#loc large
      | inl(v) => #()
      | inr(g) =>
        let lo := fst(s);
        let hi := fst(g);
        let mass := !(#loc work +ₗ lo);
        let remainder := !(#loc work +ₗ hi) + mass - #int (total : ℤ);
        (#loc probability +ₗ lo) ← mass;
        (#loc aliases +ₗ lo) ← hi;
        (#loc work +ₗ hi) ← remainder;
        (if remainder < #int (total : ℤ) then
          (#loc small ← inr((hi, snd(s))); #loc large ← snd(g))
        else #loc small ← snd(s));
        prepare #()

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

private abbrev encodeNat (n : ℕ) : Val rT := .int n

private abbrev encodeIndex {n : ℕ} (i : Fin n) : Val rT := .int i.val

private def stateOwns {n : ℕ} (work probability aliases small large : Loc)
    (s : VoseBalance.State n) : IProp GF :=
  iprop(Array.owns work (List.ofFn (encodeNat ∘ s.work)) ∗
    Array.owns probability (List.ofFn (encodeNat ∘ s.threshold)) ∗
    Array.owns aliases (List.ofFn (encodeIndex ∘ s.target)) ∗
    appHeapFrag small (listVal encodeIndex s.small) ∗
    appHeapFrag large (listVal encodeIndex s.large))

end ownership

private theorem consecutive_tail {n : ℕ} (i : Fin n) (is : List (Fin n)) (offset : ℕ)
    (h : (i :: is).map Fin.val = List.range' offset (i :: is).length) :
    i.val = offset ∧ is.map Fin.val = List.range' (offset + 1) is.length := by
  simpa only [List.map_cons, List.length_cons, List.range'_succ, Nat.add_one_mul,
    Nat.mul_one, Nat.add_zero, List.cons.injEq] using h

private theorem nat_lt_test (a b : ℕ) :
    decide ((a : ℤ) < (b : ℤ)) = decide (a < b) := by simp

private theorem listVal_map {rT : Type _} [ProbLangℝ rT] {α β : Type _}
    (encode : β → Val rT) (f : α → β) (xs : List α) :
    listVal encode (xs.map f) = listVal (encode ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, listVal, Function.comp_apply, ih]

private theorem weights_encoding {rT : Type _} [ProbLangℝ rT] (ws : List ℕ) :
    (listVal encodeNat ws : Val rT) =
      listVal (fun i : Fin ws.length => encodeNat (ws.get i)) (List.finRange ws.length) := by
  have h := congrArg (listVal (encodeNat (rT := rT))) (List.map_get_finRange ws)
  rw [listVal_map] at h
  simpa only [Function.comp_def] using h.symm

private theorem indices_consecutive (n : ℕ) :
    (List.finRange n).map Fin.val = List.range' 0 (List.finRange n).length := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

private theorem weights_sum (ws : List ℕ) : (∑ i : Fin ws.length, ws.get i) = ws.sum := by
  simpa only [List.sum_ofFn] using congrArg List.sum (List.ofFn_get ws)

private theorem positive_length (ws : List ℕ) (hs : 0 < ws.sum) : 0 < ws.length :=
  List.length_pos_iff.mpr (by intro h; simp [h] at hs)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_setup (E : CoPset) (n total : ℕ) (weights : Fin n → ℕ)
    (work probability aliases small large : Loc) (is : List (Fin n)) (offset : ℕ)
    (hindices : is.map Fin.val = List.range' offset is.length) (s : VoseBalance.State n) :
    stateOwns (rT := rT) (GF := GF) work probability aliases small large s ⊢
      tglWp E pl(&(setup n total work aliases small large)
        &(listVal (fun i => (Val.int (weights i) : Val rT)) is).fst #int (offset : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          stateOwns (rT := rT) work probability aliases small large
            (VoseBalance.State.setup total weights is s))) := by
  induction is generalizing offset s with
  | nil =>
    iintro Hstate
    isimp only [VoseBalance.State.setup]
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iframe Hstate
    itrivial
  | cons i is ih =>
    obtain ⟨hhead, htail⟩ := consecutive_tail i is offset hindices
    rw [← hhead] at htail
    iintro Hstate
    isimp only [VoseBalance.State.setup]
    isimp only [stateOwns] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    rw [← hhead]
    simp only [listVal]
    iterate 8 twp_pure
    twp_bind pl((#loc work +ₗ #int (i.val : ℤ)) ← #int ((n * weights i : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_store_vector E work encodeNat
        s.work i (n * weights i)) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    twp_pure
    twp_bind pl((#loc aliases +ₗ #int (i.val : ℤ)) ← #int (i.val : ℤ))
    iapply tglWp_wand
    isplitl [Haliases]
    · iapply (Array.twp_store_vector E aliases encodeIndex s.target i i) $$ Haliases
    iintro %v ⟨%hv, Haliases⟩
    subst v
    iterate 2 twp_pure
    rw [← Nat.cast_mul, nat_lt_test]
    by_cases hsmall : n * weights i < total
    · rw [decide_eq_true hsmall]
      twp_pure
      twp_bind pl(!#loc small)
      iapply twp_load
      iframe Hsmall
      iintro Hsmall
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex (i :: s.small))))
      iapply (twp_store (v := listVal encodeIndex (i :: s.small)))
      iframe Hsmall
      iintro Hsmall
      iterate 3 twp_pure
      have hrec := ih (i.val + 1) htail (VoseBalance.State.install total weights i s)
      simp [setup, Exp.close, Exp.closeRec] at hrec
      isimp only [Exp.ofVal]
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.install, hsmall, ite_true]
      iframe Hwork Hprobability Haliases Hsmall Hlarge
    · rw [decide_eq_false hsmall]
      twp_pure
      twp_bind pl(!#loc large)
      iapply twp_load
      iframe Hlarge
      iintro Hlarge
      twp_bind (Exp.store pl(#loc large) (Exp.ofVal (listVal encodeIndex (i :: s.large))))
      iapply (twp_store (v := listVal encodeIndex (i :: s.large)))
      iframe Hlarge
      iintro Hlarge
      iterate 3 twp_pure
      have hrec := ih (i.val + 1) htail (VoseBalance.State.install total weights i s)
      simp [setup, Exp.close, Exp.closeRec] at hrec
      isimp only [Exp.ofVal]
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.install, hsmall, ite_false]
      iframe Hwork Hprobability Haliases Hsmall Hlarge

private theorem remainder_cast (a b total : ℕ) (h : total ≤ a) :
    (a : ℤ) + b - total = ((a + b - total : ℕ) : ℤ) := by omega

private theorem twp_balance (E : CoPset) (n total : ℕ) (weights : Fin n → ℕ)
    (work probability aliases small large : Loc) (s : VoseBalance.State n)
    (hInv : VoseBalance.Invariant weights total s) :
    stateOwns (rT := rT) (GF := GF) work probability aliases small large s ⊢
      tglWp E pl(&(balance total work probability aliases small large) #())
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          stateOwns (rT := rT) work probability aliases small large (s.finish total))) := by
  revert hInv
  induction s using VoseBalance.State.finish.induct total with
  | case1 s hs =>
    intro hInv
    have hfinish : s.finish total = s := by rw [VoseBalance.State.finish, hs]
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    twp_pures
    twp_value
    imodintro
    isimp only [stateOwns, hs]
    iframe Hwork Hprobability Haliases Hsmall Hlarge
  | case2 s lo ss hs hl =>
    intro hInv
    have hfinish : s.finish total = s := by rw [VoseBalance.State.finish, hs, hl]
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs, hl] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    iterate 2 twp_pure
    twp_bind pl(!#loc large)
    iapply twp_load
    iframe Hlarge
    iintro Hlarge
    twp_pures
    twp_value
    imodintro
    isimp only [stateOwns, hs, hl]
    iframe Hwork Hprobability Haliases Hsmall Hlarge
  | case3 s lo ss hi ls hs hl ih =>
    intro hInv
    have hnext := VoseBalance.advance_invariant weights s hInv lo hi ss ls hs hl
    have hlarge := hInv.large_le hi (by simp [hl])
    have hfinish : s.finish total = (s.advance total lo hi).finish total := by
      rw [VoseBalance.State.finish, hs, hl]
    have hrec := ih hnext
    simp [balance, Exp.close, Exp.closeRec] at hrec
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs, hl] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    iterate 2 twp_pure
    twp_bind pl(!#loc large)
    iapply twp_load
    iframe Hlarge
    iintro Hlarge
    iterate 6 twp_pure
    twp_bind pl(!(#loc work +ₗ #int (lo.val : ℤ)))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_load_ofFn E work (encodeNat ∘ s.work) lo) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    twp_pure
    twp_bind pl(!(#loc work +ₗ #int (hi.val : ℤ)))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_load_ofFn E work (encodeNat ∘ s.work) hi) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    iterate 3 twp_pure
    rw [remainder_cast (s.work hi) (s.work lo) total hlarge]
    twp_bind pl((#loc probability +ₗ #int (lo.val : ℤ)) ← #int (s.work lo : ℤ))
    iapply tglWp_wand
    isplitl [Hprobability]
    · iapply (Array.twp_store_vector E probability encodeNat s.threshold lo (s.work lo))
        $$ Hprobability
    iintro %v ⟨%hv, Hprobability⟩
    subst v
    twp_pure
    twp_bind pl((#loc aliases +ₗ #int (lo.val : ℤ)) ← #int (hi.val : ℤ))
    iapply tglWp_wand
    isplitl [Haliases]
    · iapply (Array.twp_store_vector E aliases encodeIndex s.target lo hi) $$ Haliases
    iintro %v ⟨%hv, Haliases⟩
    subst v
    twp_pure
    twp_bind pl((#loc work +ₗ #int (hi.val : ℤ)) ←
      #int ((s.work hi + s.work lo - total : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_store_vector E work encodeNat s.work hi
        (s.work hi + s.work lo - total)) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    iterate 2 twp_pure
    rw [nat_lt_test]
    by_cases hr : s.work hi + s.work lo - total < total
    · rw [decide_eq_true hr]
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex (hi :: ss))))
      iapply (twp_store (v := listVal encodeIndex (hi :: ss)))
      iframe Hsmall
      iintro Hsmall
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc large) (Exp.ofVal (listVal encodeIndex ls)))
      iapply (twp_store (v := listVal encodeIndex ls))
      iframe Hlarge
      iintro Hlarge
      twp_pure
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.advance, hs, hl, List.tail_cons, hr, ite_true]
      iframe Hwork Hprobability Haliases Hsmall Hlarge
    · rw [decide_eq_false hr]
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex ss)))
      iapply (twp_store (v := listVal encodeIndex ss))
      iframe Hsmall
      iintro Hsmall
      twp_pure
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.advance, hs, hl, List.tail_cons, hr, ite_false]
      iframe Hwork Hprobability Haliases Hsmall Hlarge

/-- Preprocessing allocates a concrete table and returns ownership of both output arrays. -/
theorem twp_voseTable (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.voseTable &(listVal encodeNat ws).fst)
      (fun v : Val rT => iprop(∃ t : AliasMass.Table ws.length ws.sum,
        ∃ probability aliases : Loc,
          ⌜v = AliasTable.value ws.length ws.sum probability aliases ∧
            ∀ i, t.mass i = ws.length * ws.get i⌝ ∗
          AliasTable.owns (rT := rT) t probability aliases)) := by
  have hn := positive_length ws hs
  let : NeZero ws.length := ⟨hn.ne'⟩
  have hInv := VoseBalance.initialized_invariant (total := ws.sum) ws.get
  have hinit : VoseBalance.State.setup ws.sum ws.get (List.finRange ws.length)
      (VoseBalance.State.blank ws.length ws.sum) =
      VoseBalance.State.initialized ws.sum ws.get := rfl
  isimp [Occil.WeightedVariants.voseTable, Exp.close, Exp.closeRec]
  twp_pure
  simp only [WeightedValidation.validWeights_openRec, ArraySyntax.length_openRec,
    WeightedValidation.sumInts_openRec]
  twp_bind pl(&Occil.Weighted.validWeights &(listVal encodeNat ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws hs
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listVal encodeNat ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E encodeNat ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal encodeNat ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #0))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := Val.int 0) (Int.natCast_pos.mpr hn))
  iintro %work Hwork
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Hwork
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #int (ws.sum : ℤ)))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := Val.int ws.sum) (Int.natCast_pos.mpr hn))
  iintro %probability Hprobability
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Hprobability
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #0))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := Val.int 0) (Int.natCast_pos.mpr hn))
  iintro %aliases Haliases
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Haliases
  twp_pure
  twp_bind (Exp.alloc (Exp.ofVal (Val.inl Val.unit : Val rT)))
  iapply (twp_alloc (v := Val.inl Val.unit))
  iintro %small Hsmall
  twp_pure
  twp_bind (Exp.alloc (Exp.ofVal (Val.inl Val.unit : Val rT)))
  iapply (twp_alloc (v := Val.inl Val.unit))
  iintro %large Hlarge
  iterate 2 twp_pure
  rw [weights_encoding ws]
  twp_bind pl(&(setup ws.length ws.sum work aliases small large)
    &(listVal (fun i : Fin ws.length => encodeNat (ws.get i)) (List.finRange ws.length)).fst #0)
  iapply tglWp_wand
  isplitl [Hwork Hprobability Haliases Hsmall Hlarge]
  · iapply (twp_setup E ws.length ws.sum ws.get work probability aliases small large
      (List.finRange ws.length) 0 (indices_consecutive ws.length)
      (VoseBalance.State.blank ws.length ws.sum))
    isimp only [stateOwns, VoseBalance.State.blank, Function.comp_def, List.ofFn_const,
      listVal, encodeNat, encodeIndex]
    iframe Hwork Hprobability Haliases Hsmall Hlarge
  iintro %v ⟨%hv, Hstate⟩
  subst v
  isimp only [hinit] at Hstate
  iterate 2 twp_pure
  twp_bind pl(&(balance ws.sum work probability aliases small large) #())
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply (twp_balance E ws.length ws.sum ws.get work probability aliases small large
      (VoseBalance.State.initialized ws.sum ws.get) hInv) $$ Hstate
  iintro %v ⟨%hv, Hstate⟩
  subst v
  twp_pures
  twp_value
  imodintro
  iexists VoseBalance.finishedTable ws.get (VoseBalance.State.initialized ws.sum ws.get) hInv
  iexists probability, aliases
  isplit
  · ipureintro
    exact ⟨rfl, VoseBalance.finishedTable_mass ws.get _ hInv (weights_sum ws)⟩
  · isimp only [AliasTable.owns, VoseBalance.finishedTable]
    isimp only [stateOwns, Function.comp_def, encodeNat, encodeIndex] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iframe Hprobability Haliases

end specification

end

end SampLib.VoseTable
