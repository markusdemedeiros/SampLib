import SampLib.Templates

/-! # Finite iteration of countable-state probability kernels -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FiniteKernels

noncomputable section

variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- The state after a fixed number of transitions. -/
def iterate (K : α → Measure α) : ℕ → α → Measure α
  | 0, x => Measure.dirac x
  | n + 1, x => (K x).bind (iterate K n)

instance (K : α → Measure α) [∀ x, IsProbabilityMeasure (K x)] (n : ℕ) (x : α) :
    IsProbabilityMeasure (iterate K n x) := by
  induction n generalizing x with
  | zero => dsimp [iterate]; infer_instance
  | succ n ih =>
    constructor
    rw [iterate, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- Conditioning on the first transition gives the iterated-kernel expectation. -/
theorem expectation (K : α → Measure α) (n : ℕ) (x : α) (F : α → ℝ≥0∞) :
    ∫⁻ y, (∫⁻ z, F z ∂iterate K n y) ∂K x = ∫⁻ z, F z ∂iterate K (n + 1) x := by
  rw [iterate, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]

/-- An invariant law remains invariant after every finite number of transitions. -/
theorem invariant (K : α → Measure α) (μ : Measure α) (h : μ.bind K = μ) (n : ℕ) :
    μ.bind (iterate K n) = μ := by
  induction n with
  | zero => exact Measure.bind_dirac
  | succ n ih =>
    change μ.bind (fun x => (K x).bind (iterate K n)) = μ
    rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable, h, ih]

/-- On a finite state space, detailed balance implies invariance. -/
theorem invariant_of_detailed_balance [Fintype α] (K : α → Measure α)
    [∀ x, IsProbabilityMeasure (K x)] (μ : Measure α)
    (h : ∀ x y, (K x) {y} * μ {x} = (K y) {x} * μ {y}) : μ.bind K = μ := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (measurableSet_singleton y)
    (measurable_of_countable _).aemeasurable, lintegral_fintype]
  simp_rw [h]
  rw [← Finset.sum_mul]
  have hsum : (∑ x, (K y) {x}) = 1 := by
    simpa only [lintegral_fintype, one_mul] using
      (show (∫⁻ _ : α, (1 : ℝ≥0∞) ∂K y) = 1 by simp)
  rw [hsum, one_mul]

/-- The successive states, excluding the initial state. -/
def trajectory (K : α → Measure α) : ℕ → α → Measure (List α)
  | 0, _ => Measure.dirac []
  | n + 1, x => (K x).bind (fun y => (trajectory K n y).map (List.cons y))

instance (K : α → Measure α) [∀ x, IsProbabilityMeasure (K x)] (n : ℕ) (x : α) :
    IsProbabilityMeasure (trajectory K n x) := by
  induction n generalizing x with
  | zero => dsimp [trajectory]; infer_instance
  | succ n ih =>
    constructor
    rw [trajectory, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp [Measure.map_apply (measurable_of_countable (List.cons _))]

/-- Path expectations condition on the first state and then prepend it. -/
theorem trajectory_expectation (K : α → Measure α) (n : ℕ) (x : α)
    (F : List α → ℝ≥0∞) :
    ∫⁻ y, (∫⁻ ys, F (y :: ys) ∂trajectory K n y) ∂K x =
      ∫⁻ ys, F ys ∂trajectory K (n + 1) x := by
  rw [trajectory, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  simp only [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Apply successive coordinate kernels, starting at coordinate `i`. -/
def sweep (K : ℕ → α → Measure α) : ℕ → ℕ → α → Measure α
  | _, 0, x => Measure.dirac x
  | i, n + 1, x => (K i x).bind (sweep K (i + 1) n)

instance (K : ℕ → α → Measure α) [∀ i x, IsProbabilityMeasure (K i x)]
    (i n : ℕ) (x : α) : IsProbabilityMeasure (sweep K i n x) := by
  induction n generalizing i x with
  | zero => dsimp [sweep]; infer_instance
  | succ n ih =>
    constructor
    rw [sweep, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- Each coordinate call receives the expectation over the remaining coordinates. -/
theorem sweep_expectation (K : ℕ → α → Measure α) (i n : ℕ) (x : α)
    (F : α → ℝ≥0∞) :
    ∫⁻ y, (∫⁻ z, F z ∂sweep K (i + 1) n y) ∂K i x =
      ∫⁻ z, F z ∂sweep K i (n + 1) x := by
  rw [sweep, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]

/-- Coordinate kernels preserving the same target preserve it after a complete sweep. -/
theorem sweep_invariant (K : ℕ → α → Measure α) (μ : Measure α)
    (h : ∀ i, μ.bind (K i) = μ) (i n : ℕ) : μ.bind (sweep K i n) = μ := by
  induction n generalizing i with
  | zero => exact Measure.bind_dirac
  | succ n ih =>
    change μ.bind (fun x => (K i x).bind (sweep K (i + 1) n)) = μ
    rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable, h i, ih]

end

end SampLib.FiniteKernels
