import SampLib.Combinatorial.Laws.Shuffle
import SampLib.Common.Laws.BooleanEvent
import SampLib.Discrete.Laws.Binomial

/-! # Permutation test law

Each replicate draws a fresh uniform positional permutation. Ties count as exceedances, so
the exceedance count is binomial with the exact null exceedance probability.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PermutationTest

noncomputable section

variable {α : Type _}

/-- Ties belong to the exceedance event. -/
def exceeds (xs : List α) (statistic : List α → ℤ)
    (σ : Equiv.Perm (Fin xs.length)) : Bool :=
  decide (statistic xs ≤ statistic (Shuffle.output xs σ))

/-- The exact null exceedance probability, retaining all positional multiplicities. -/
def bias (xs : List α) (statistic : List α → ℤ) : unitInterval :=
  BooleanEvent.bias (Shuffle.law xs) (exceeds xs statistic)

/-- The number of independently sampled null exceedances. -/
abbrev law (xs : List α) (statistic : List α → ℤ) (n : ℕ) :=
  Binomial.law (bias xs statistic) n

/-- Condition on one uniform null permutation, then count the remaining trials. -/
theorem expectation (xs : List α) (statistic : List α → ℤ) (n z : ℕ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ σ, ∫⁻ k,
        F (if exceeds xs statistic σ then z + 1 + k else z + k)
          ∂law xs statistic n ∂Shuffle.law xs =
      ∫⁻ k, F (z + k) ∂law xs statistic (n + 1) := by
  rw [BooleanEvent.expectation (Shuffle.law xs) (exceeds xs statistic)
    (measurable_of_countable _)
    (fun b => ∫⁻ k, F (if b then z + 1 + k else z + k) ∂law xs statistic n)]
  simpa only [law, Binomial.continuation, bias, add_ite, apply_ite, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using
    Binomial.expectation (bias xs statistic) n (fun k => F (z + k))

end

end SampLib.PermutationTest
