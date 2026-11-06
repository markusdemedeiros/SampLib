import SampLib.Distributions.MetropolisRatio

/-! # Countable-state Metropolis proposal laws

The exact singleton probabilities tie the rational Hastings callback to the
normalized proposal law. Countability determines the whole law from these atoms.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.CountableMetropolisHastings

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- A normalized countable proposal with exact rational transition probabilities. -/
structure Proposal (α : Type _) [MeasurableSpace α] extends MetropolisRatio.Ratios α where
  measure : α → Measure α
  probability : ∀ x, IsProbabilityMeasure (measure x)
  singleton : ∀ x y, measure x {y} =
    ((numerator x y : ℝ≥0∞) / denominator x y)

instance (p : Proposal α) (x : α) : IsProbabilityMeasure (p.measure x) := p.probability x

abbrev law (w : α → ℕ) (p : Proposal α) :=
  MetropolisRatio.law w p.toRatios p.measure

omit [MeasurableSingletonClass α] in
/-- Zero forward probabilities cannot occur in a sampled proposal. -/
theorem proposal_support (p : Proposal α) (x : α) :
    ∀ᵐ y ∂p.measure x, 0 < p.numerator x y := by
  apply ae_iff_of_countable.mpr
  intro y hy
  by_contra h
  apply hy
  rw [p.singleton]
  simp [Nat.eq_zero_of_not_pos h]

end

end SampLib.CountableMetropolisHastings

namespace SampLib.CountableMetropolis

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- The symmetric-proposal acceptance ratio is the target-weight ratio. -/
def ratios : MetropolisRatio.Ratios α := ⟨fun _ _ => 1, fun _ _ => 1, by simp⟩

/-- This finite-step law is defined for every normalized proposal kernel.
Symmetry is relevant to target invariance, rather than to the execution law. -/
abbrev law (w : α → ℕ) (μ : α → Measure α) := MetropolisRatio.law w ratios μ

end

end SampLib.CountableMetropolis
