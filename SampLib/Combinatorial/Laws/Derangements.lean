module

public import SampLib.Combinatorial.Laws.Sattolo
public import Mathlib.Combinatorics.Derangements.Finite

@[expose] public section

/-! # Uniform derangements by conditioning uniform permutations -/

open Equiv MeasureTheory Measure
open scoped ENNReal Classical

namespace SampLib.DerangementLaw

noncomputable section

/-- A cycle with at least two positions has no fixed point. -/
theorem fullCycle_derangement {n : ℕ} (hn : 2 ≤ n) {σ : Perm (Fin n)}
    (hσ : SattoloLaw.FullCycle σ) : σ ∈ derangements (Fin n) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro i hi
  obtain ⟨j, hj⟩ := exists_ne i
  exact hj ((hσ i j).eq_of_left hi).symm

theorem nonempty (n : ℕ) (hn : n ≠ 1) : (derangements (Fin n)).Nonempty := by
  cases n with
  | zero => exact ⟨Equiv.refl _, fun i => i.elim0⟩
  | succ n =>
    obtain ⟨σ⟩ := (inferInstance : Nonempty (SattoloLaw.Cycle (n + 1)))
    exact ⟨σ.val, fullCycle_derangement (by omega) σ.property⟩

@[simp] theorem derangements_one : derangements (Fin 1) = ∅ := by
  ext σ
  simp only [derangements, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_forall, not_not]
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Acceptance is possible exactly outside the singleton case, including the empty permutation. -/
theorem acceptance_nonzero (n : ℕ) (hn : n ≠ 1) :
    Permutations.law n (derangements (Fin n)) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := nonempty n hn
  have hpos : Permutations.law n {σ} ≠ 0 := by simp [Permutations.law_singleton]
  exact fun h => hpos (measure_mono_null (Set.singleton_subset_iff.mpr hσ) h)

@[simp] theorem acceptance_one : Permutations.law 1 (derangements (Fin 1)) = 0 := by simp

/-- The acceptance probability is the derangement count divided by the permutation count. -/
theorem acceptance_mass (n : ℕ) :
    Permutations.law n (derangements (Fin n)) = (numDerangements n : ℝ≥0∞) / n.factorial := by
  rw [Permutations.law, Measure.uniformOfFinset_apply]
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Fintype.card_subtype, card_derangements_fin_eq_numDerangements]

/-- Uniform permutations conditioned to have no fixed points. -/
def law (n : ℕ) (_hn : n ≠ 1) : Measure (Perm (Fin n)) :=
  (Permutations.law n (derangements (Fin n)))⁻¹ •
    (Permutations.law n).restrict (derangements (Fin n))

instance (n : ℕ) (hn : n ≠ 1) : IsProbabilityMeasure (law n hn) where
  measure_univ := by
    simp [law, ENNReal.inv_mul_cancel (acceptance_nonzero n hn)
      (measure_ne_top (Permutations.law n) _)]

/-- The conditioned law is uniform on exactly the fixed-point-free permutations. -/
theorem law_singleton (n : ℕ) (hn : n ≠ 1) (σ : Perm (Fin n)) :
    law n hn {σ} = if σ ∈ derangements (Fin n) then (numDerangements n : ℝ≥0∞)⁻¹ else 0 := by
  have hfactorial : (n.factorial : ℝ≥0∞) ≠ 0 := by positivity
  simp only [law, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton σ)]
  by_cases hσ : σ ∈ derangements (Fin n)
  · rw [Set.singleton_inter_of_mem hσ, Permutations.law_singleton, acceptance_mass,
      ENNReal.inv_div (Or.inl (by finiteness)) (Or.inl hfactorial),
      ENNReal.div_eq_inv_mul, mul_assoc,
      ENNReal.mul_inv_cancel hfactorial (by finiteness), mul_one, ite_eq_left hσ]
  · rw [Set.singleton_inter_of_notMem hσ, measure_empty, mul_zero, ite_eq_right hσ]

end

end SampLib.DerangementLaw
