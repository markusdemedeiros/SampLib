module

public import SampLib.Combinatorial.Laws.Choice
public import SampLib.Core.Laws.Permutations

@[expose] public section

/-! # Uniform position permutations for Fisher–Yates

Choosing the last position uniformly and recursing on the rest gives the uniform
permutation law.
-/

open Equiv MeasureTheory
open scoped ENNReal

namespace SampLib.Shuffle

noncomputable section

/-- The latent position permutation, independent of the list's values. -/
abbrev law {α : Type*} (xs : List α) := Permutations.law xs.length

/-- Decode a position permutation to the corresponding list entries. -/
def output {α : Type*} (xs : List α) (σ : Perm (Fin xs.length)) : List α :=
  List.ofFn (xs.get ∘ σ)

/-- Credit of the last position's uniform rank. -/
def rankCredit (n : ℕ) (F : Perm (Fin (n + 1)) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ σ, F ((Permutations.decomposeLast n).symm (Choice.position (n + 1) k, σ))
    ∂Permutations.law n

theorem rank_expectation (n : ℕ) (F : Perm (Fin (n + 1)) → ℝ≥0∞) :
    (∑ k ∈ Finset.range (n + 1), rankCredit n F k) / ((n + 1 : ℕ) : ℝ≥0∞) =
      ∫⁻ σ, F σ ∂Permutations.law (n + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (rankCredit n F) (n + 1), Permutations.expectation]
  simp only [Nat.cast_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rankCredit]
  rw [Choice.position_of_lt i.val i.isLt]

end

end SampLib.Shuffle
