module

public import SampLib.Combinatorial.Laws.Sattolo
public import SampLib.Combinatorial.Laws.Choice

@[expose] public section

/-! # Uniform ranks for Sattolo insertion

Inserting the next position after a uniformly ranked earlier position preserves the
uniform full-cycle law.
-/

open Equiv MeasureTheory
open scoped ENNReal

namespace SampLib.Sattolo

noncomputable section

/-- The latent full cycle, independent of the list's values. -/
abbrev law {α : Type*} (xs : List α) := SattoloLaw.law xs.length

/-- Decode a position permutation to the corresponding list entries. -/
def output {α : Type*} (xs : List α) (σ : SattoloLaw.Cycle xs.length) : List α :=
  List.ofFn (xs.get ∘ σ.val)

/-- Credit of a uniform rank for the newly inserted position. -/
def rankCredit (n : ℕ) (F : SattoloLaw.Cycle (n + 2) → ℝ≥0∞)
    (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ σ, F (SattoloLaw.insert (Choice.position (n + 1) k) σ) ∂SattoloLaw.law (n + 1)

theorem rank_expectation (n : ℕ) (F : SattoloLaw.Cycle (n + 2) → ℝ≥0∞) :
    (∑ k ∈ Finset.range (n + 1), rankCredit n F k) / ((n + 1 : ℕ) : ℝ≥0∞) =
      ∫⁻ σ, F σ ∂SattoloLaw.law (n + 2) := by
  rw [← Fin.sum_univ_eq_sum_range (rankCredit n F) (n + 1), SattoloLaw.expectation]
  simp only [Nat.cast_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rankCredit]
  rw [Choice.position_of_lt i.val i.isLt]

end

end SampLib.Sattolo
