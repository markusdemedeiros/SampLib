import SampLib.Weighted.Support.FenwickPropagation

/-! # Replacing a Fenwick weight

The signed difference updates the total and exactly the ancestor nodes of the
changed position. The postcondition allows the new total to be zero.
-/

open ProbLang

namespace SampLib.FenwickSet

private theorem guard {n : ℕ} (j : Fin n) :
    Bool.or (Bool.or false (decide ((n : ℤ) ≤ j.val))) false = false := by
  have hj : ¬ (n : ℤ) ≤ j.val := by exact_mod_cast Nat.not_le.mpr j.isLt
  simp [hj]

private theorem total_replacement {n : ℕ} (w : Fin n → ℕ) (j : Fin n) (value : ℕ) :
    ((List.ofFn w).sum : ℤ) + ((value : ℤ) - w j) =
      ((List.ofFn (Function.update w j value)).sum : ℤ) := by
  simpa only [List.sum_ofFn, add_sub_assoc] using
    (FenwickMath.total_update_int w j value).symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Replace any valid position by a nonnegative weight, preserving the complete representation. -/
theorem twp_fenwickSet (E : CoPset) {n : ℕ} (w : Fin n → ℕ)
    (total values tree : Loc) (j : Fin n) (value : ℕ) :
    FenwickTable.owns w total values tree ⊢
      tglWp E pl(&Occil.WeightedVariants.fenwickSet
        &(FenwickTable.value n total values tree).fst #int (j.val : ℤ) #int (value : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗
          FenwickTable.owns (Function.update w j value) total values tree)) := by
  have hprop := FenwickPropagation.twp_replace (GF := GF) E w j value tree (j.val + 1)
    (Nat.zero_lt_succ _) (FenwickMath.contains_self (Nat.zero_lt_succ _))
  simp only [FenwickMath.partialTree_initial] at hprop
  dsimp [FenwickPropagation.replace, Exp.close, Exp.closeRec] at hprop
  simp only [LowBit.lowBit_closeRec] at hprop
  isimp only [FenwickTable.owns]
  iintro ⟨Htotal, Hvalues, Htree⟩
  isimp only [Occil.WeightedVariants.fenwickSet, Exp.close, Exp.closeRec,
    LowBit.lowBit_closeRec]
  twp_pures
  rw [guard j]
  twp_pure
  twp_bind pl(!(#loc values +ₗ #int (j.val : ℤ)))
  iapply tglWp_wand
  isplitl [Hvalues]
  · iapply (Array.twp_load_ofFn E values (FenwickTable.natVal ∘ w) j) $$ Hvalues
  iintro %v ⟨%hv, Hvalues⟩
  subst v
  twp_pures
  twp_bind pl(!#loc total)
  iapply twp_load
  iframe Htotal
  iintro Htotal
  twp_pures
  rw [total_replacement w j value]
  twp_bind (Exp.store pl(#loc total)
    (Exp.ofVal (FenwickTable.natVal (List.ofFn (Function.update w j value)).sum)))
  iapply twp_store
  iframe Htotal
  iintro Htotal
  twp_pure
  twp_bind pl((#loc values +ₗ #int (j.val : ℤ)) ← #int (value : ℤ))
  iapply tglWp_wand
  isplitl [Hvalues]
  · iapply (Array.twp_store_vector E values FenwickTable.natVal w j value) $$ Hvalues
  iintro %v ⟨%hv, Hvalues⟩
  subst v
  iterate 3 twp_pure
  simp only [LowBit.lowBit_openRec]
  iapply tglWp_wand
  isplitl [Htree]
  · iapply hprop $$ Htree
  iintro %v ⟨%hv, Htree⟩
  iframe Htotal Hvalues Htree
  itrivial

end specification

end SampLib.FenwickSet
