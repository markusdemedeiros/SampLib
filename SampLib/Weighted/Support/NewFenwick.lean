import SampLib.Weighted.Support.FenwickPropagation
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.Arrays

/-! # Allocating a Fenwick table

Initialization installs each weight along its ancestor chain. The returned
locations own the total, original weights, and every exact dyadic interval sum.
-/

open ProbLang

namespace SampLib.NewFenwick

private def buildTree {rT : Type} (n : ℕ) (tree : Loc) : Exp rT := pl%
  rec build xs i := case! xs
    | inl(v) => #()
    | inr(p) =>
      (&(FenwickPropagation.add n tree) i (fst(p)); build (snd(p)) (i + #1))

private theorem consecutive_tail {n : ℕ} (j : Fin n) (js : List (Fin n)) (offset : ℕ)
    (h : (j :: js).map Fin.val = List.range' offset (j :: js).length) :
    j.val = offset ∧ js.map Fin.val = List.range' (offset + 1) js.length := by
  simpa only [List.map_cons, List.length_cons, List.range'_succ, Nat.add_one_mul,
    Nat.mul_one, Nat.add_zero, List.cons.injEq] using h

private theorem listVal_map {rT : Type} [ProbLangℝ rT] {α β : Type}
    (encode : β → Val rT) (f : α → β) (xs : List α) :
    listVal encode (xs.map f) = listVal (encode ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, listVal, Function.comp_apply, ih]

private theorem weights_encoding {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    (listVal FenwickTable.natVal ws : Val rT) =
      listVal (fun j : Fin ws.length => FenwickTable.natVal (ws.get j))
        (List.finRange ws.length) := by
  have h := congrArg (listVal (FenwickTable.natVal (rT := rT))) (List.map_get_finRange ws)
  rw [listVal_map] at h
  exact h.symm

private theorem indices_consecutive (n : ℕ) :
    (List.finRange n).map Fin.val = List.range' 0 (List.finRange n).length := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_buildTree (E : CoPset) {n : ℕ} (w : Fin n → ℕ) (tree : Loc)
    (js : List (Fin n)) (offset : ℕ)
    (hindices : js.map Fin.val = List.range' offset js.length) :
    Array.owns tree (List.ofFn (FenwickTable.natVal (rT := rT) ∘
      (fun k : Fin (n + 1) => FenwickMath.cell (FenwickMath.prefixWeights w offset) k.val))) ⊢
      tglWp E pl(&(buildTree n tree)
        &(listVal (fun j => FenwickTable.natVal (w j)) js).fst
        #int ((offset + 1 : ℕ) : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ Array.owns tree (List.ofFn
          (FenwickTable.natVal (rT := rT) ∘ (fun k : Fin (n + 1) =>
            FenwickMath.cell (FenwickMath.prefixWeights w (offset + js.length)) k.val))))) := by
  induction js generalizing offset with
  | nil =>
    iintro Htree
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    isimp only [List.length_nil, Nat.add_zero]
    iframe Htree
  | cons j js IH =>
    obtain ⟨hhead, htail⟩ := consecutive_tail j js offset hindices
    subst offset
    have hfinish : j.val + (j :: js).length = (j.val + 1) + js.length := by
      simp only [List.length_cons]
      omega
    rw [hfinish]
    have hprop := FenwickPropagation.twp_add (GF := GF) E
      (FenwickMath.prefixWeights w j.val) j (w j) tree (j.val + 1)
      (Nat.zero_lt_succ _) (FenwickMath.contains_self (Nat.zero_lt_succ _))
    simp only [FenwickMath.prefixWeights_current, Nat.cast_zero, sub_zero,
      FenwickMath.partialTree_initial, FenwickMath.prefixWeights_succ] at hprop
    have hrec := IH (j.val + 1) htail
    dsimp [buildTree, Exp.close, Exp.closeRec] at hrec
    simp only [FenwickPropagation.add_closeRec] at hrec
    iintro Htree
    simp only [listVal]
    isimp only [buildTree, Exp.close, Exp.closeRec, FenwickPropagation.add_closeRec]
    iterate 6 twp_pure
    twp_bind pl(&(FenwickPropagation.add n tree) #int ((j.val + 1 : ℕ) : ℤ)
      #int (w j : ℤ))
    iapply tglWp_wand
    isplitl [Htree]
    · iapply hprop $$ Htree
    iintro %v ⟨%hv, Htree⟩
    subst v
    iterate 3 twp_pure
    simp only [Exp.ofVal, Nat.cast_add, FenwickPropagation.add_openRec]
    iapply tglWp_wand
    isplitl [Htree]
    · iapply hrec $$ Htree
    iintro %v ⟨%hv, Htree⟩
    iframe Htree
    itrivial

/-- Positive-total natural weights allocate a table with exact, owned cumulative sums. -/
theorem twp_newFenwick (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.newFenwick
      &(listVal (FenwickTable.natVal (rT := rT)) ws).fst)
      (fun v => iprop(∃ total values tree : Loc,
        ⌜v = FenwickTable.value ws.length total values tree⌝ ∗
          FenwickTable.owns (rT := rT) ws.get total values tree)) := by
  have hn : 0 < ws.length := List.length_pos_iff.mpr (by intro h; simp [h] at hs)
  have hencoding : List.ofFn (FenwickTable.natVal (rT := rT) ∘ ws.get) =
      ws.map FenwickTable.natVal := by rw [← List.map_ofFn, List.ofFn_get]
  isimp [Occil.WeightedVariants.newFenwick, Exp.close, Exp.closeRec]
  twp_pure
  simp only [WeightedValidation.validWeights_openRec, ArraySyntax.length_openRec,
    WeightedValidation.sumInts_openRec, ArraySyntax.fillArray_openRec]
  twp_bind pl(&Occil.Weighted.validWeights &(listVal FenwickTable.natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws hs
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listVal FenwickTable.natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E FenwickTable.natVal ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal FenwickTable.natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_bind (Exp.alloc (Exp.ofVal (FenwickTable.natVal ws.sum)))
  iapply twp_alloc
  iintro %total Htotal
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #0))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := Val.int 0) (Int.natCast_pos.mpr hn))
  iintro %values Hvalues
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Hvalues
  twp_pures
  rw [← Nat.cast_add_one]
  twp_bind pl(allocN(#int ((ws.length + 1 : ℕ) : ℤ), #0))
  iapply (twp_allocN (n := ((ws.length + 1 : ℕ) : ℤ)) (v := Val.int 0)
    (Int.natCast_pos.mpr (Nat.zero_lt_succ _)))
  iintro %tree Htree
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Htree
  twp_pure
  twp_bind pl(&Occil.fillArray #loc values &(listVal FenwickTable.natVal ws).fst #0)
  iapply tglWp_wand
  isplitl [Hvalues]
  · iapply (Array.twp_fillArray E values FenwickTable.natVal ws
      (List.replicate ws.length (Val.int 0)) (by simp) 0)
    isimp only [Nat.cast_zero, add_zero]
    iexact Hvalues
  iintro %v ⟨%hv, Hvalues⟩
  subst v
  iterate 3 twp_pure
  rw [weights_encoding ws]
  twp_bind pl(&(buildTree ws.length tree)
    &(listVal (fun j : Fin ws.length => FenwickTable.natVal (ws.get j))
      (List.finRange ws.length)).fst #1)
  iapply tglWp_wand
  isplitl [Htree]
  · iapply (twp_buildTree E ws.get tree (List.finRange ws.length) 0
      (indices_consecutive ws.length))
    isimp only [FenwickMath.prefixWeights_zero, FenwickMath.cell_zero_weights,
      Function.comp_def, List.ofFn_const]
    iexact Htree
  iintro %v ⟨%hv, Htree⟩
  subst v
  twp_pures
  twp_value
  imodintro
  iexists total, values, tree
  isplit
  · ipureintro
    rfl
  · isimp only [FenwickTable.owns, List.ofFn_get, hencoding]
    isimp only [List.length_finRange, Nat.zero_add, FenwickMath.prefixWeights_length] at Htree
    isimp only [Nat.cast_zero, add_zero] at Hvalues
    iframe Htotal Hvalues Htree

end specification

end SampLib.NewFenwick
