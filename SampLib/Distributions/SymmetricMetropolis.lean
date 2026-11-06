import SampLib.Distributions.MetropolisRatio

/-! # Symmetric-proposal Metropolis

The proposal probabilities cancel in the acceptance ratio. Symmetry of the
proposal and the smaller opposing target weights give detailed balance.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.SymmetricMetropolis

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

def ratios : MetropolisRatio.Ratios α := ⟨fun _ _ => 1, fun _ _ => 1, by simp⟩

omit [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] in
@[simp] private theorem weight_ratios :
    MetropolisRatio.weight (ratios : MetropolisRatio.Ratios α) = fun _ _ => 1 := by
  funext x y
  simp [MetropolisRatio.weight, ratios]

abbrev kernel (w : α → ℕ) (p : Metropolis.Proposal α) :=
  MetropolisRatio.kernel w ratios (Metropolis.proposal p)

abbrev law (w : α → ℕ) (p : Metropolis.Proposal α) := FiniteKernels.iterate (kernel w p)

abbrev target (w : α → ℕ) (h : 0 < ∑ x, w x) :=
  Metropolis.target (fun x => (w x : ℝ≥0)) (by exact_mod_cast h)

private theorem kernel_singleton_of_ne (w : α → ℕ) (p : Metropolis.Proposal α)
    (x y : α) (h : x ≠ y) :
    kernel w p x {y} = RealCoin.pmf (Metropolis.bias (fun x => (w x : ℝ≥0))
      (MetropolisRatio.weight ratios) x y) true * (p.mass x y : ℝ≥0∞) := by
  classical
  rw [kernel, MetropolisRatio.kernel, Measure.bind_apply (measurableSet_singleton y)
    (measurable_of_countable _).aemeasurable, lintegral_fintype]
  simp [MetropolisRatio.selection, h, Metropolis.proposal_singleton, Pi.single_apply, eq_comm]

/-- Symmetric proposals leave the normalized target weights invariant. -/
theorem detailed_balance (w : α → ℕ) (p : Metropolis.Proposal α)
    (hsym : ∀ x y, p.mass x y = p.mass y x) (h : 0 < ∑ x, w x) (x y : α) :
    (kernel w p x) {y} * (target w h) {x} =
      (kernel w p y) {x} * (target w h) {y} := by
  by_cases hxy : x = y
  · subst y
    rfl
  rw [kernel_singleton_of_ne w p x y hxy,
    kernel_singleton_of_ne w p y x (Ne.symm hxy),
    Metropolis.target_singleton, Metropolis.target_singleton, weight_ratios]
  have hflux := congrArg (fun t : ℝ≥0 =>
    (t : ℝ≥0∞) * (p.mass x y : ℝ≥0∞) / (∑ z, w z : ℝ≥0))
    (Metropolis.flux_symm (fun x => (w x : ℝ≥0)) (fun _ _ => 1) x y)
  simpa [RealCoin.pmf, Metropolis.bias,
    ENNReal.coe_mul, ENNReal.div_eq_inv_mul, hsym y x,
    mul_comm, mul_left_comm, mul_assoc] using hflux

/-- Every finite iterate preserves the target; it need not reach it from a fixed state. -/
theorem invariant (w : α → ℕ) (p : Metropolis.Proposal α)
    (hsym : ∀ x y, p.mass x y = p.mass y x) (h : 0 < ∑ x, w x) (n : ℕ) :
    (target w h).bind (law w p n) = target w h :=
  FiniteKernels.invariant _ _
    (FiniteKernels.invariant_of_detailed_balance _ _ (detailed_balance w p hsym h)) n

end

end SampLib.SymmetricMetropolis
