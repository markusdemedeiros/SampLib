import SampLib.FenwickTable
import SampLib.ArrayVectorLoc
import SampLib.Distributions.FenwickPropagation
import SampLib.LowBit

/-! # Updating the ancestor chain of one Fenwick weight

The constructor passes the increment as a second argument; replacement captures
it in a one-argument closure. Both source recursions use the same partial-tree invariant.
-/

open ProbLang

namespace SampLib.FenwickPropagation

def replace {rT : Type} (n : ℕ) (tree : Loc) (difference : ℤ) : Exp rT := pl%
  rec propagate i :=
    if #int (n : ℤ) < i then #() else
      let previous := !(#loc tree +ₗ i);
      (#loc tree +ₗ i) ← (previous + #int difference);
      propagate (i + &Occil.WeightedVariants.lowBit i)

def add {rT : Type} (n : ℕ) (tree : Loc) : Exp rT := pl%
  rec propagate i amount :=
    if #int (n : ℤ) < i then #() else
      let previous := !(#loc tree +ₗ i);
      (#loc tree +ₗ i) ← (previous + amount);
      propagate (i + &Occil.WeightedVariants.lowBit i) amount

theorem add_lc {rT : Type} (n : ℕ) (tree : Loc) :
    (add n tree : Exp rT).IsLocallyClosed := by is_lc

theorem add_fv {rT : Type} (n : ℕ) (tree : Loc) : (add n tree : Exp rT).fv = ∅ := by
  simp [add, Exp.fv, LowBit.lowBit_fv]

@[simp] theorem add_openRec {rT : Type} (n : ℕ) (tree : Loc) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (add n tree) = add n tree :=
  (Exp.open_lc k e _ (add_lc n tree)).symm

@[simp] theorem add_closeRec {rT : Type} (n : ℕ) (tree : Loc) (k : ℕ) (x : Var) :
    Exp.closeRec k x (add n tree : Exp rT) = add n tree :=
  Exp.closeRec_fresh x _ k (by simp [add_fv])

private theorem stop_test (n i : ℕ) :
    decide ((n : ℤ) < i) = decide (n < i) := by simp

private theorem replacement_value {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value i : ℕ)
    (h : FenwickMath.contains (j.val + 1) i) :
    (FenwickMath.cell w i : ℤ) + ((value : ℤ) - w j) =
      (FenwickMath.cell (Function.update w j value) i : ℤ) := by
  simpa only [h, ite_true] using (FenwickMath.cell_update_int w j value i).symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_replace (E : CoPset) {n : ℕ} (w : Fin n → ℕ) (j : Fin n)
    (value : ℕ) (tree : Loc) (i : ℕ) (hi : 0 < i)
    (hc : FenwickMath.contains (j.val + 1) i) :
    Array.owns tree (List.ofFn (FenwickTable.natVal (rT := rT) ∘
      FenwickMath.partialTree w j value i)) ⊢
      tglWp E pl(&(replace n tree ((value : ℤ) - w j)) #int (i : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ Array.owns tree
          (List.ofFn (FenwickTable.natVal (rT := rT) ∘
            (fun k : Fin (n + 1) => FenwickMath.cell (Function.update w j value) k.val))))) := by
  generalize hsteps : n + 1 - i = steps
  induction steps using Nat.strong_induction_on generalizing i with
  | h steps IH =>
    by_cases hn : n < i
    · iintro Htree
      isimp only [FenwickMath.partialTree_done w j value i hn] at Htree
      isimp only [replace, Exp.close, Exp.closeRec, LowBit.lowBit_closeRec]
      twp_pures
      rw [stop_test, decide_eq_true hn]
      twp_pures
      twp_value
      imodintro
      iframe Htree
      itrivial
    · let k : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le (Nat.le_of_not_gt hn)⟩
      have hcurrent : FenwickMath.partialTree w j value i k = FenwickMath.cell w i :=
        FenwickMath.partialTree_current w j value k
      have hnext : Function.update (FenwickMath.partialTree w j value i) k
          (FenwickMath.cell (Function.update w j value) i) =
          FenwickMath.partialTree w j value (i + FenwickMath.lowBit i) :=
        FenwickMath.partialTree_advance w j value k hc
      have hmeasure : n + 1 - (i + FenwickMath.lowBit i) < steps := by
        rw [← hsteps]
        exact FenwickMath.propagation_measure hi (Nat.le_of_not_gt hn)
      have hrec := IH _ hmeasure (i + FenwickMath.lowBit i) (by omega)
        (FenwickMath.contains_parent hc) rfl
      dsimp [replace, Exp.close, Exp.closeRec] at hrec
      simp only [LowBit.lowBit_closeRec] at hrec
      iintro Htree
      isimp only [replace, Exp.close, Exp.closeRec, LowBit.lowBit_closeRec]
      twp_pures
      rw [stop_test, decide_eq_false hn]
      twp_pure
      twp_bind pl(!(#loc tree +ₗ #int (i : ℤ)))
      iapply tglWp_wand
      isplitl [Htree]
      · iapply (Array.twp_load_ofFn E tree
          (FenwickTable.natVal ∘ FenwickMath.partialTree w j value i) k) $$ Htree
      iintro %v ⟨%hv, Htree⟩
      subst v
      rw [Function.comp_apply, hcurrent]
      twp_pures
      rw [replacement_value w j value i hc]
      twp_bind (Exp.store pl(#loc (tree + (i : ℤ)))
        (Exp.ofVal (FenwickTable.natVal (FenwickMath.cell (Function.update w j value) i))))
      iapply tglWp_wand
      isplitl [Htree]
      · iapply (Array.twp_store_vector_loc E tree FenwickTable.natVal
          (FenwickMath.partialTree w j value i) k
          (FenwickMath.cell (Function.update w j value) i)) $$ Htree
      iintro %v ⟨%hv, Htree⟩
      subst v
      isimp only [hnext] at Htree
      twp_pure
      isimp only [LowBit.lowBit_openRec]
      twp_bind pl(&Occil.WeightedVariants.lowBit #int (i : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply LowBit.twp_lowBit E i hi
      iintro %v %hv
      subst v
      twp_pure
      iapply hrec $$ Htree

theorem twp_add (E : CoPset) {n : ℕ} (w : Fin n → ℕ) (j : Fin n)
    (value : ℕ) (tree : Loc) (i : ℕ) (hi : 0 < i)
    (hc : FenwickMath.contains (j.val + 1) i) :
    Array.owns tree (List.ofFn (FenwickTable.natVal (rT := rT) ∘
      FenwickMath.partialTree w j value i)) ⊢
      tglWp E pl(&(add n tree) #int (i : ℤ) #int ((value : ℤ) - w j))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ Array.owns tree
          (List.ofFn (FenwickTable.natVal (rT := rT) ∘
            (fun k : Fin (n + 1) => FenwickMath.cell (Function.update w j value) k.val))))) := by
  generalize hsteps : n + 1 - i = steps
  induction steps using Nat.strong_induction_on generalizing i with
  | h steps IH =>
    by_cases hn : n < i
    · iintro Htree
      isimp only [FenwickMath.partialTree_done w j value i hn] at Htree
      isimp only [add, Exp.close, Exp.closeRec, LowBit.lowBit_closeRec]
      twp_pures
      rw [stop_test, decide_eq_true hn]
      twp_pures
      twp_value
      imodintro
      iframe Htree
      itrivial
    · let k : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le (Nat.le_of_not_gt hn)⟩
      have hcurrent : FenwickMath.partialTree w j value i k = FenwickMath.cell w i :=
        FenwickMath.partialTree_current w j value k
      have hnext : Function.update (FenwickMath.partialTree w j value i) k
          (FenwickMath.cell (Function.update w j value) i) =
          FenwickMath.partialTree w j value (i + FenwickMath.lowBit i) :=
        FenwickMath.partialTree_advance w j value k hc
      have hmeasure : n + 1 - (i + FenwickMath.lowBit i) < steps := by
        rw [← hsteps]
        exact FenwickMath.propagation_measure hi (Nat.le_of_not_gt hn)
      have hrec := IH _ hmeasure (i + FenwickMath.lowBit i) (by omega)
        (FenwickMath.contains_parent hc) rfl
      dsimp [add, Exp.close, Exp.closeRec] at hrec
      simp only [LowBit.lowBit_closeRec] at hrec
      iintro Htree
      isimp only [add, Exp.close, Exp.closeRec, LowBit.lowBit_closeRec]
      twp_pures
      rw [stop_test, decide_eq_false hn]
      twp_pure
      twp_bind pl(!(#loc tree +ₗ #int (i : ℤ)))
      iapply tglWp_wand
      isplitl [Htree]
      · iapply (Array.twp_load_ofFn E tree
          (FenwickTable.natVal ∘ FenwickMath.partialTree w j value i) k) $$ Htree
      iintro %v ⟨%hv, Htree⟩
      subst v
      rw [Function.comp_apply, hcurrent]
      twp_pures
      rw [replacement_value w j value i hc]
      twp_bind (Exp.store pl(#loc (tree + (i : ℤ)))
        (Exp.ofVal (FenwickTable.natVal (FenwickMath.cell (Function.update w j value) i))))
      iapply tglWp_wand
      isplitl [Htree]
      · iapply (Array.twp_store_vector_loc E tree FenwickTable.natVal
          (FenwickMath.partialTree w j value i) k
          (FenwickMath.cell (Function.update w j value) i)) $$ Htree
      iintro %v ⟨%hv, Htree⟩
      subst v
      isimp only [hnext] at Htree
      twp_pure
      isimp only [LowBit.lowBit_openRec]
      twp_bind pl(&Occil.WeightedVariants.lowBit #int (i : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply LowBit.twp_lowBit E i hi
      iintro %v %hv
      subst v
      twp_pure
      simp only [Exp.ofVal]
      iapply hrec $$ Htree

end specification

end SampLib.FenwickPropagation
