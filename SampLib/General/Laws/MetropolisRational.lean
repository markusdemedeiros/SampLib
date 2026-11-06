import SampLib.General.Laws.Metropolis

/-! # Exact rational proposal interfaces for Metropolis–Hastings -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.MetropolisHastings

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

/-- Rational transition probabilities, including a positive denominator for zero entries. -/
structure Proposal (α : Type _) [Fintype α] where
  numerator : α → α → ℕ
  denominator : α → α → ℕ
  denominator_pos : ∀ x y, 0 < denominator x y
  total : ∀ x, ∑ y, (numerator x y : ℝ≥0) / denominator x y = 1

def stochastic (p : Proposal α) : Metropolis.Proposal α :=
  ⟨fun x y => (p.numerator x y : ℝ≥0) / p.denominator x y, p.total⟩

abbrev kernel (w : α → ℕ) (p : Proposal α) :=
  Metropolis.kernel (fun x => (w x : ℝ≥0)) (stochastic p)

abbrev law (w : α → ℕ) (p : Proposal α) := FiniteKernels.iterate (kernel w p)

/-- The integer target weights, normalized to a probability law. -/
abbrev target (w : α → ℕ) (h : 0 < ∑ x, w x) : Measure α :=
  Metropolis.target (fun x => (w x : ℝ≥0)) (by exact_mod_cast h)

/-- Detailed balance preserves the target under every finite number of transitions. -/
theorem invariant (w : α → ℕ) (p : Proposal α) (h : 0 < ∑ x, w x) (n : ℕ) :
    (target w h).bind (law w p n) = target w h :=
  FiniteKernels.invariant _ _ (Metropolis.invariant _ (stochastic p) _) n

/-- Every sampled proposal has positive forward numerator. -/
theorem proposal_support (p : Proposal α) (x : α) :
    ∀ᵐ y ∂Metropolis.proposal (stochastic p) x, 0 < p.numerator x y := by
  apply ae_iff_of_countable.mpr
  intro y hy
  by_contra h
  apply hy
  rw [Metropolis.proposal_singleton]
  simp [stochastic, Nat.eq_zero_of_not_pos h]

end

end SampLib.MetropolisHastings
