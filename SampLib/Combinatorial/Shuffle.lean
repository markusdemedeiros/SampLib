import SampLib.Core.ArrayPermutation
import SampLib.Combinatorial.Choice
import SampLib.Core.Syntax.Arrays
import Samplers.Combinatorial.Basic

/-! # Fisher–Yates sampling of position permutations

The target is uniform over original positions. Coincident entries retain their
separate positions throughout the mathematical law.
-/

open ProbLang Equiv
open scoped ENNReal

namespace SampLib.Shuffle

open ArrayPermutation

noncomputable section

/-- The latent position permutation, independent of the list's values. -/
abbrev law {α : Type*} (xs : List α) := Permutations.law xs.length

/-- Decode a position permutation to the corresponding list entries. -/
def output {α : Type*} (xs : List α) (σ : Perm (Fin xs.length)) : List α :=
  List.ofFn (xs.get ∘ σ)

private def loop {rT : Type} (l : Loc) : Exp rT := pl%
  rec go i := if i <= #0 then #() else
    let j := &Occil.uniformInt (i + #1);
    let x := !(#loc l +ₗ i);
    let y := !(#loc l +ₗ j);
    (#loc l +ₗ i) ← y;
    (#loc l +ₗ j) ← x;
    go (i - #1)

section mathematics

open MeasureTheory

private def rankCredit (n : ℕ) (F : Perm (Fin (n + 1)) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ σ, F ((Permutations.decomposeLast n).symm (Choice.position (n + 1) k, σ))
    ∂Permutations.law n

private theorem rank_expectation (n : ℕ) (F : Perm (Fin (n + 1)) → ℝ≥0∞) :
    (∑ k ∈ Finset.range (n + 1), rankCredit n F k) / ((n + 1 : ℕ) : ℝ≥0∞) =
      ∫⁻ σ, F σ ∂Permutations.law (n + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (rankCredit n F) (n + 1), Permutations.expectation]
  simp only [Nat.cast_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rankCredit]
  rw [Choice.position_of_lt i.val i.isLt]

private theorem ofFn_encode {rT : Type} [ProbLangℝ rT] (encode : α → Val rT)
    (xs : List α) :
    List.ofFn (fun i : Fin xs.length => encode (xs.get i)) = xs.map encode := by
  simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map encode) (List.ofFn_get xs)

private theorem listVal_map {rT : Type} [ProbLangℝ rT] (encode : α → Val rT)
    (xs : List α) : listVal id (xs.map encode) = listVal encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH => simp only [List.map_cons, listVal, id_eq, IH]

private theorem encode_output {rT : Type} [ProbLangℝ rT] (encode : α → Val rT)
    (xs : List α) (σ : Perm (Fin xs.length)) :
    listVal id (List.ofFn ((fun i => encode (xs.get i)) ∘ σ)) =
      listVal encode (output xs σ) := by
  have hmap : List.ofFn ((fun i => encode (xs.get i)) ∘ σ) =
      (List.ofFn (xs.get ∘ σ)).map encode := by
    simpa only [Function.comp_def] using
      (List.map_ofFn (f := xs.get ∘ σ) (g := encode)).symm
  rw [hmap, listVal_map]
  rfl

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (l : Loc) (n : ℕ)
    (a : Fin (n + 1) → Val rT) (F : Perm (Fin (n + 1)) → ℝ≥0∞) :
    Array.owns l (List.ofFn a) ⊢ ↯ (∫⁻ σ, F σ ∂Permutations.law (n + 1)) -∗
      tglWp E pl(&(loop (rT := rT) l) #int (n : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ ∃ σ : Perm (Fin (n + 1)),
          Array.owns l (List.ofFn (a ∘ σ)) ∗ ↯ (F σ))) := by
  induction n with
  | zero =>
    have hcredit : (∫⁻ σ, F σ ∂Permutations.law (0 + 1)) =
        F (Equiv.refl (Fin (0 + 1))) := Permutations.expectation_one F
    iintro Harray Hcredit
    twp_pures
    twp_value
    imodintro
    isplit
    · itrivial
    · iexists (Equiv.refl _)
      isimp only [Function.comp_def, Equiv.refl_apply]
      isimp only [hcredit] at Hcredit
      iframe Harray Hcredit
  | succ n IH =>
    iintro Harray Hcredit
    iterate 5 twp_pure
    simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
    rw [← Nat.cast_add_one]
    twp_bind pl(&Occil.uniformInt #int ((n + 2 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (UniformInt.twp_uniformInt E (n + 2) (Nat.succ_pos (n + 1)) (rankCredit (n + 1) F))
      rw [rank_expectation]
      iexact Hcredit
    iintro %v ⟨%j, %hv, %hj, Hcredit⟩
    subst v
    let i : Fin (n + 2) := ⟨j, hj⟩
    twp_pure
    twp_bind pl(!(#loc l +ₗ #int ((n + 1 : ℕ) : ℤ)))
    iapply tglWp_wand
    isplitl [Harray]
    · have hload := Array.twp_load_ofFn (GF := GF) E l a (Fin.last (n + 1))
      simp only [Fin.val_last] at hload
      iapply hload $$ Harray
    iintro %x ⟨%hx, Harray⟩
    subst x
    twp_pure
    twp_bind pl(!(#loc l +ₗ #int (j : ℤ)))
    iapply tglWp_wand
    isplitl [Harray]
    · iapply (Array.twp_load_ofFn E l a i) $$ Harray
    iintro %y ⟨%hy, Harray⟩
    subst y
    twp_pure
    twp_bind pl((#loc l +ₗ #int ((n + 1 : ℕ) : ℤ)) ← &(a i).fst)
    iapply tglWp_wand
    isplitl [Harray]
    · have hstore := Array.twp_store_ofFn (GF := GF) E l a (Fin.last (n + 1)) (a i)
      simp only [Fin.val_last] at hstore
      iapply hstore $$ Harray
    iintro %w ⟨%hw, Harray⟩
    subst w
    twp_pure
    twp_bind pl((#loc l +ₗ #int (j : ℤ)) ← &(a (Fin.last (n + 1))).fst)
    iapply tglWp_wand
    isplitl [Harray]
    · iapply (Array.twp_store_index E l ((List.ofFn a).set (n + 1) (a i))
        ⟨j, by simpa only [List.length_set, List.length_ofFn] using hj⟩
        (a (Fin.last (n + 1)))) $$ Harray
    iintro %w ⟨%hw, Harray⟩
    subst w
    have hsplit := owns_after_swap (GF := GF) l (n + 1) a i
    simp only [i] at hsplit
    isimp only [i] at Harray
    isimp only [hsplit] at Harray
    ihave ⟨Hprefix, Hlast⟩ := Harray
    isimp only [rankCredit, Choice.position_of_lt j hj] at Hcredit
    have hrec := IH (afterSwap a i)
      (fun σ => F ((Permutations.decomposeLast (n + 1)).symm (i, σ)))
    simp [-List.ofFn_succ, loop, Exp.close, Exp.closeRec, i] at hrec
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    simp only [UniformInt.uniformInt_openRec]
    iapply tglWp_wand
    isplitl [Hprefix Hcredit]
    · iapply hrec $$ Hprefix Hcredit
    iintro %v ⟨%hv, %σ, Hprefix, Hcredit⟩
    iframe %hv
    iexists (Permutations.decomposeLast (n + 1)).symm (i, σ)
    isimp only [owns_after_shuffle]
    isimp only [i, Nat.cast_add_one]
    iframe Hprefix Hlast Hcredit

/-- Initialize, shuffle in place, and return the encoded permuted entries. -/
theorem twp_shuffle (E : CoPset) (encode : α → Val rT) (xs : List α)
    (F : Perm (Fin xs.length) → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ σ, F σ ∂law xs) -∗
      tglWp E pl(&Occil.shuffle &(listVal encode xs).fst)
        (fun v => iprop(∃ σ : Perm (Fin xs.length),
          ⌜v = listVal encode (output xs σ)⌝ ∗ ↯ (F σ))) := by
  iintro Hcredit
  twp_pure
  simp only [ArraySyntax.length_openRec, ArraySyntax.length_closeRec,
    ArraySyntax.fillArray_openRec, ArraySyntax.fillArray_closeRec,
    ArraySyntax.readArray_openRec, ArraySyntax.readArray_closeRec,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E encode xs
  iintro %v %hv
  subst v
  cases xs with
  | nil =>
    have hcredit : (∫⁻ σ, F σ ∂law ([] : List α)) = F (Equiv.refl _) :=
      Permutations.expectation_zero F
    twp_pures
    twp_value
    imodintro
    iexists (Equiv.refl _)
    isimp only [hcredit] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | cons x xs =>
    simp only [List.length_cons]
    twp_pures
    twp_bind pl(allocN(#int ((xs.length + 1 : ℕ) : ℤ), #()))
    iapply (twp_allocN (n := ((xs.length + 1 : ℕ) : ℤ)) (v := Val.unit)
      (Int.natCast_pos.mpr (Nat.succ_pos xs.length)))
    iintro %l Harray
    isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Harray
    twp_pure
    twp_bind pl(&Occil.fillArray #loc l &(listVal encode (x :: xs)).fst #0)
    iapply tglWp_wand
    isplitl [Harray]
    · have hfill := Array.twp_fillArray (GF := GF) E l encode (x :: xs)
        (List.replicate (xs.length + 1) Val.unit) (by simp) 0
      simp only [Nat.cast_zero, add_zero] at hfill
      iapply hfill $$ Harray
    iintro %w ⟨%hw, Harray⟩
    subst w
    isimp only [← ofFn_encode encode (x :: xs)] at Harray
    isimp only [law, List.length_cons] at Hcredit
    iterate 3 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&(loop (rT := rT) l) #int (xs.length : ℤ))
    iapply tglWp_wand
    isplitl [Harray Hcredit]
    · iapply (twp_loop E l xs.length (fun i => encode ((x :: xs).get i)) F)
        $$ Harray Hcredit
    iintro %v ⟨%hv, %σ, Harray, Hcredit⟩
    subst v
    twp_pure
    twp_bind pl(&Occil.readArray #loc l #0 #int ((xs.length + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Harray]
    · have hread := Array.twp_readArray (GF := GF) E l
        (List.ofFn ((fun i => encode ((x :: xs).get i)) ∘ σ)) 0
      simp only [Nat.cast_zero, add_zero, Nat.zero_add, List.length_ofFn] at hread
      iapply hread $$ Harray
    iintro %v ⟨%hv, Harray⟩
    iapply (tglWp_value (v := v))
    iexists σ
    iframe Hcredit
    ipureintro
    exact hv.trans (encode_output encode (x :: xs) σ)

/-- Uniform position permutations, including empty lists and duplicate values. -/
theorem shuffle_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α) :
    IsDistSpec (GF := GF) E pl(&Occil.shuffle &(listVal encode xs).fst)
      (law xs) (fun σ => listVal encode (output xs σ)) where
  spec F _ := wand_entails (twp_shuffle E encode xs F)

end specification

end

end SampLib.Shuffle
