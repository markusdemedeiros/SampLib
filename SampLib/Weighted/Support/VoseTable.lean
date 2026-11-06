import SampLib.Weighted.Support.VosePairing

/-! # Constructing owned Vose alias tables -/

open ProbLang

namespace SampLib.VoseTable

noncomputable section

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
