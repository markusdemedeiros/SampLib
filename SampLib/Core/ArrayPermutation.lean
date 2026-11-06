import SampLib.Core.ArrayOwnership
import SampLib.Core.Laws.Permutations

/-! # Array invariants for permutation samplers -/

open ProbLang Equiv

namespace SampLib.ArrayPermutation

noncomputable section

/-- Prefix contents after swapping the final entry with position `i`. -/
def afterSwap {α : Type*} {n : ℕ} (a : Fin (n + 1) → α)
    (i : Fin (n + 1)) : Fin n → α :=
  fun j => a (Equiv.swap (Fin.last n) i j.castSucc)

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- Separate the finalized last cell from the still-active prefix. -/
theorem owns_after_swap (l : Loc) (n : ℕ) (a : Fin (n + 1) → Val rT)
    (i : Fin (n + 1)) :
    Array.owns (GF := GF) l
        (((List.ofFn a).set n (a i)).set i (a (Fin.last n))) =
      iprop(Array.owns l (List.ofFn (afterSwap a i)) ∗ appHeapFrag (l + n) (a i)) := by
  have hs := Permutations.ofFn_swap a (Fin.last n) i
  simp only [Fin.val_last] at hs
  rw [hs, List.ofFn_succ_last, Array.owns_append]
  simp only [Function.comp_apply, List.length_ofFn, Equiv.swap_apply_left,
    Array.owns, sep_emp.to_eq]
  rfl

/-- Reassemble the prefix and final cell into their full position permutation. -/
theorem owns_after_shuffle (l : Loc) (n : ℕ) (a : Fin (n + 1) → Val rT)
    (i : Fin (n + 1)) (σ : Perm (Fin n)) :
    Array.owns (GF := GF) l
        (List.ofFn (a ∘ (Permutations.decomposeLast n).symm (i, σ))) =
      iprop(Array.owns l (List.ofFn (afterSwap a i ∘ σ)) ∗ appHeapFrag (l + n) (a i)) := by
  rw [Permutations.ofFn_decomposeLast, Array.owns_append]
  simp only [afterSwap, Function.comp_def, List.length_ofFn, Array.owns, sep_emp.to_eq]

end ownership

end

end SampLib.ArrayPermutation
