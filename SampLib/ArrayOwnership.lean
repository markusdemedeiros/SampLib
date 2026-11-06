import SampLib.ListEncoding
import Metrology.Iris.Array
import Samplers.Combinatorial.Basic

/-! # Ownership and access for finite heap arrays -/

open ProbLang

namespace SampLib.Array

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- Consecutive cells containing a mathematical list of values. -/
def owns (l : Loc) : List (Val rT) → IProp GF
  | [] => emp
  | v :: vs => iprop(appHeapFrag l v ∗ owns (l + 1) vs)

theorem owns_replicate (l : Loc) (v : Val rT) (n : ℕ) :
    owns (GF := GF) l (List.replicate n v) = appArrayFrag l v n := by
  induction n generalizing l with
  | zero => rfl
  | succ n IH => simp only [List.replicate_succ, owns, appArrayFrag, IH]

private theorem offset_succ (l : Loc) (i : ℕ) :
    l + ((i : ℤ) + 1) = (l + 1) + i := by ring

/-- Ownership splits at a list boundary. -/
theorem owns_append (l : Loc) (xs ys : List (Val rT)) :
    owns (GF := GF) l (xs ++ ys) =
      iprop(owns l xs ∗ owns (l + (xs.length : ℤ)) ys) := by
  induction xs generalizing l with
  | nil =>
    simp only [List.nil_append, owns, List.length_nil, Nat.cast_zero, add_zero]
    exact emp_sep.to_eq.symm
  | cons v xs IH =>
    simp only [List.cons_append, owns, List.length_cons, Nat.cast_add_one]
    rw [IH, sep_assoc.to_eq, offset_succ]

/-- Focus one cell, retaining the continuation that reinstalls its replacement. -/
theorem access (l : Loc) (vs : List (Val rT)) (i : Fin vs.length) :
    owns l vs ⊢ iprop(appHeapFrag (l + (i : ℕ)) (vs.get i) ∗
      ∀ v : Val rT, appHeapFrag (l + (i : ℕ)) v -∗ owns l (vs.set i v)) := by
  induction vs generalizing l with
  | nil => exact Fin.elim0 i
  | cons v vs IH =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.val_zero, Nat.cast_zero, add_zero, List.get_cons_zero,
        List.set_cons_zero, owns]
      iintro ⟨Hv, Hvs⟩
      iframe Hv
      iintro %w Hw
      iframe Hw Hvs
    · simp only [List.get_eq_getElem, Fin.val_succ, Nat.cast_add, Nat.cast_one,
        List.getElem_cons_succ,
        List.set_cons_succ, owns]
      iintro ⟨Hv, Hvs⟩
      ihave ⟨Hi, Hrestore⟩ := IH (l + 1) i $$ Hvs
      rw [offset_succ]
      iframe Hi
      iintro %w Hw
      iframe Hv
      iapply Hrestore $$ Hw

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reading preserves ownership of the complete array. -/
theorem twp_load_index (E : CoPset) (l : Loc) (vs : List (Val rT))
    (i : Fin vs.length) :
    owns l vs ⊢ tglWp E pl(!(#loc l +ₗ #int (i.val : ℤ)))
      (fun v => iprop(⌜v = vs.get i⌝ ∗ owns l vs)) := by
  iintro Harray
  ihave ⟨Hi, Hrestore⟩ := access l vs i $$ Harray
  twp_pures
  iapply twp_load
  iframe Hi
  iintro Hi
  ihave Harray := Hrestore $$ %(vs.get i) Hi
  isimp only [List.get_eq_getElem, List.set_getElem_self] at Harray
  iframe Harray
  itrivial

/-- Writing changes precisely the indexed cell. -/
theorem twp_store_index (E : CoPset) (l : Loc) (vs : List (Val rT))
    (i : Fin vs.length) (v : Val rT) :
    owns l vs ⊢ tglWp E pl((#loc l +ₗ #int (i.val : ℤ)) ← &v.fst)
      (fun w => iprop(⌜w = Val.unit⌝ ∗ owns l (vs.set i v))) := by
  iintro Harray
  ihave ⟨Hi, Hrestore⟩ := access l vs i $$ Harray
  twp_pures
  iapply twp_store
  iframe Hi
  iintro Hi
  ihave Harray := Hrestore $$ %v Hi
  iframe Harray
  itrivial

/-- Vector-indexed reads avoid transporting a list-length bound at call sites. -/
theorem twp_load_ofFn (E : CoPset) (l : Loc) {n : ℕ} (a : Fin n → Val rT)
    (i : Fin n) :
    owns l (List.ofFn a) ⊢ tglWp E pl(!(#loc l +ₗ #int (i.val : ℤ)))
      (fun v => iprop(⌜v = a i⌝ ∗ owns l (List.ofFn a))) := by
  simpa only [List.get_eq_getElem, List.getElem_ofFn] using
    twp_load_index (GF := GF) E l (List.ofFn a)
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

/-- Vector-indexed writes retain the ordinary list-update invariant. -/
theorem twp_store_ofFn (E : CoPset) (l : Loc) {n : ℕ} (a : Fin n → Val rT)
    (i : Fin n) (v : Val rT) :
    owns l (List.ofFn a) ⊢ tglWp E pl((#loc l +ₗ #int (i.val : ℤ)) ← &v.fst)
      (fun w => iprop(⌜w = Val.unit⌝ ∗ owns l ((List.ofFn a).set i v))) :=
  twp_store_index E l (List.ofFn a)
    ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩ v

/-- Initialization consumes a block of the right size and installs the list. -/
theorem twp_fillArray (E : CoPset) (l : Loc) (encode : α → Val rT)
    (xs : List α) (vs : List (Val rT)) (h : vs.length = xs.length) (i : ℕ) :
    owns (l + (i : ℤ)) vs ⊢
      tglWp E pl(&Occil.fillArray #loc l &(listVal encode xs).fst #int (i : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ owns (l + (i : ℤ)) (xs.map encode))) := by
  induction xs generalizing vs i with
  | nil =>
    have hv : vs = [] := by simpa using h
    subst vs
    iintro Harray
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    isimp only [List.map_nil]
    iframe Harray
  | cons x xs IH =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      have htail : vs.length = xs.length := by simpa using h
      iintro Harray
      isimp only [owns] at Harray
      ihave ⟨Hv, Hvs⟩ := Harray
      simp only [listVal]
      twp_pures
      twp_bind (Exp.store pl(#loc (l + (i : ℤ))) (Exp.ofVal (encode x)))
      iapply twp_store
      iframe Hv
      iintro Hx
      iterate 3 twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&Occil.fillArray #loc l &(listVal encode xs).fst
        #int ((i + 1 : ℕ) : ℤ))
      iapply tglWp_wand
      isplitl [Hvs]
      · iapply IH vs htail (i + 1)
        isimp only [Nat.cast_add_one, add_assoc] at Hvs
        isimp only [Nat.cast_add_one, add_assoc]
        iexact Hvs
      iintro %w ⟨%hw, Hvs⟩
      iapply (tglWp_value (v := w))
      iframe %hw
      isimp only [List.map_cons, owns, Nat.cast_add_one, add_assoc]
      isimp only [Nat.cast_add_one, add_assoc] at Hvs
      iframe Hx Hvs

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem read_test (i n : ℕ) :
    ((i : ℤ) == ((i + (n + 1) : ℕ) : ℤ)) = false := by
  exact beq_eq_false_iff_ne.mpr (by omega)

private theorem read_bound (i n : ℕ) : i + (n + 1) = (i + 1) + n := by omega

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem cons_expr (v : Val rT) (vs : List (Val rT)) :
    Exp.inr (.pair v.fst (.ofVal (listVal id vs))) =
      Exp.ofVal (listVal id (v :: vs)) := rfl

/-- Reading an interval returns its list while retaining all of its cells. -/
theorem twp_readArray (E : CoPset) (l : Loc) (vs : List (Val rT)) (i : ℕ) :
    owns (l + (i : ℤ)) vs ⊢
      tglWp E pl(&Occil.readArray #loc l #int (i : ℤ) #int ((i + vs.length : ℕ) : ℤ))
        (fun v => iprop(⌜v = listVal id vs⌝ ∗ owns (l + (i : ℤ)) vs)) := by
  induction vs generalizing i with
  | nil =>
    iintro Harray
    simp only [List.length_nil, Nat.add_zero, listVal]
    twp_pures
    rw [beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iframe Harray
    itrivial
  | cons v vs IH =>
    iintro Harray
    isimp only [owns] at Harray
    ihave ⟨Hv, Hvs⟩ := Harray
    simp only [List.length_cons]
    twp_pures
    rw [int_beq, read_test]
    twp_pures
    twp_bind pl(!#loc (l + (i : ℤ)))
    iapply twp_load
    iframe Hv
    iintro Hv
    iterate 2 twp_pure
    rw [← Nat.cast_add_one]
    rw [read_bound i vs.length]
    simp only [Exp.ofVal]
    twp_bind pl(&Occil.readArray #loc l #int ((i + 1 : ℕ) : ℤ)
      #int (((i + 1) + vs.length : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hvs]
    · iapply IH (i + 1)
      isimp only [Nat.cast_add_one, add_assoc]
      isimp only [add_assoc] at Hvs
      iexact Hvs
    iintro %w ⟨%hw, Hvs⟩
    subst w
    rw [cons_expr]
    iapply (tglWp_value (v := listVal id (v :: vs)))
    isimp only [owns, add_assoc]
    iframe Hv
    isimp only [Nat.cast_add_one, add_assoc] at Hvs
    iexact Hvs

end specification

end SampLib.Array
