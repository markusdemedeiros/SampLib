module

public import Mathlib.GroupTheory.Perm.Fin
public import Metrology.ProbLang.Measure
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Uniform permutations and the last-position decomposition -/

open Equiv MeasureTheory Measure
open scoped ENNReal

namespace SampLib.Permutations

noncomputable section

instance (n : ℕ) : MeasurableSpace (Perm (Fin n)) := ⊤
instance (n : ℕ) : MeasurableSingletonClass (Perm (Fin n)) := ⟨fun _ => trivial⟩

/-- Every position permutation has equal probability. -/
def law (n : ℕ) : Measure (Perm (Fin n)) := uniformOfFinset Finset.univ

instance (n : ℕ) : IsProbabilityMeasure (law n) :=
  isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

/-- Each position permutation has reciprocal-factorial mass. -/
theorem law_singleton (n : ℕ) (σ : Perm (Fin n)) :
    law n {σ} = (n.factorial : ℝ≥0∞)⁻¹ := by
  simp [law, uniformOfFinset_apply_singleton, Fintype.card_perm]

@[simp] theorem expectation_zero (F : Perm (Fin 0) → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law 0 = F (Equiv.refl _) := by
  have hf : F = fun _ => F (Equiv.refl _) :=
    funext fun σ => congrArg F (Subsingleton.elim σ _)
  rw [hf]
  simp

@[simp] theorem expectation_one (F : Perm (Fin 1) → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law 1 = F (Equiv.refl _) := by
  have hf : F = fun _ => F (Equiv.refl _) :=
    funext fun σ => congrArg F (Subsingleton.elim σ _)
  rw [hf]
  simp

/-- Select the image of the last position, then permute the other positions. -/
def decomposeLast (n : ℕ) : Perm (Fin (n + 1)) ≃ Fin (n + 1) × Perm (Fin n) :=
  ((Equiv.permCongr finSuccEquivLast).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr finSuccEquivLast.symm (Equiv.refl _))

@[simp] theorem decomposeLast_symm_last (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) :
    (decomposeLast n).symm (i, σ) (Fin.last n) = i := by
  simp [decomposeLast, Equiv.permCongr_def]

@[simp] theorem decomposeLast_symm_castSucc (n : ℕ) (i : Fin (n + 1))
    (σ : Perm (Fin n)) (j : Fin n) :
    (decomposeLast n).symm (i, σ) j.castSucc =
      Equiv.swap (Fin.last n) i (σ j).castSucc := by
  have h : some (σ j) = finSuccEquivLast i ↔ (σ j).castSucc = i := by
    rw [← finSuccEquivLast_castSucc (σ j)]
    exact finSuccEquivLast.injective.eq_iff
  by_cases he : (σ j).castSucc = i <;>
    simp [decomposeLast, Equiv.permCongr_def, Equiv.swap_apply_def, h, he]

/-- A uniform permutation is a uniform last choice and an independent smaller permutation. -/
theorem expectation (n : ℕ) (F : Perm (Fin (n + 1)) → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law (n + 1) =
      (∑ i : Fin (n + 1), ∫⁻ σ, F ((decomposeLast n).symm (i, σ)) ∂law n) /
        (n + 1 : ℕ) := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure, lintegral_dirac,
    lintegral_smul_measure, smul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Finset.mul_sum]
  rw [← (decomposeLast n).symm.sum_comp F, Fintype.sum_prod_type]
  simp only [Nat.factorial_succ, Nat.cast_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  ring

/-- Replacing one vector coordinate agrees with list-array update. -/
theorem ofFn_update {α : Type*} {n : ℕ} (a : Fin n → α) (i : Fin n) (v : α) :
    List.ofFn (Function.update a i v) = (List.ofFn a).set i v := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [List.getElem_set, Function.update, Fin.ext_iff, eq_comm]

/-- The two writes in an array swap implement the corresponding transposition. -/
theorem ofFn_swap {α : Type*} {n : ℕ} (a : Fin n → α) (i j : Fin n) :
    ((List.ofFn a).set i (a j)).set j (a i) = List.ofFn (a ∘ Equiv.swap i j) := by
  rw [Equiv.swap_comm i j, Equiv.comp_swap_eq_update, ofFn_update, ofFn_update]

/-- The smaller shuffled prefix and the chosen final entry form the full permutation. -/
theorem ofFn_decomposeLast {α : Type*} (n : ℕ) (a : Fin (n + 1) → α)
    (i : Fin (n + 1)) (σ : Perm (Fin n)) :
    List.ofFn (a ∘ (decomposeLast n).symm (i, σ)) =
      List.ofFn (fun j => a (Equiv.swap (Fin.last n) i (σ j).castSucc)) ++ [a i] := by
  rw [List.ofFn_succ_last]
  simp only [Function.comp_apply, decomposeLast_symm_castSucc, decomposeLast_symm_last]

end

end SampLib.Permutations
