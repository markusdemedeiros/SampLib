import SampLib.General.Laws.FiniteKernels
import SampLib.Uniform.Laws.RealCoin

/-! # The Metropolis acceptance flux

Acceptance retains the smaller of the two opposing proposal flows. This identity
is the mathematical reason that the resulting transition preserves its target.
-/

open scoped ENNReal NNReal

namespace SampLib.Metropolis

noncomputable section

variable {α : Type _}

/-- The accepted fraction of a directed proposal flow; zero flow is never accepted. -/
def acceptance (w : α → ℝ≥0) (q : α → α → ℝ≥0) (x y : α) : ℝ≥0 :=
  min (w x * q x y) (w y * q y x) / (w x * q x y)

theorem acceptance_le_one (w : α → ℝ≥0) (q : α → α → ℝ≥0) (x y : α) :
    acceptance w q x y ≤ 1 := by
  by_cases h : w x * q x y = 0
  · simp [acceptance, h]
  · rw [acceptance, div_le_one (pos_iff_ne_zero.mpr h)]
    exact min_le_left _ _

/-- A proposal contributes exactly the smaller opposing flow. -/
theorem accepted_flux (w : α → ℝ≥0) (q : α → α → ℝ≥0) (x y : α) :
    w x * q x y * acceptance w q x y = min (w x * q x y) (w y * q y x) := by
  by_cases h : w x * q x y = 0
  · simp [acceptance, h]
  · dsimp [acceptance]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ h]

/-- The accepted flow is symmetric, including zero target or proposal weights. -/
theorem flux_symm (w : α → ℝ≥0) (q : α → α → ℝ≥0) (x y : α) :
    w x * q x y * acceptance w q x y = w y * q y x * acceptance w q y x := by
  rw [accepted_flux, accepted_flux, min_comm]

def bias (w : α → ℝ≥0) (q : α → α → ℝ≥0) (x y : α) : unitInterval :=
  ⟨acceptance w q x y, NNReal.coe_nonneg _, by exact_mod_cast acceptance_le_one w q x y⟩

section finite

open MeasureTheory Measure

variable [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

/-- A finite stochastic proposal matrix. -/
structure Proposal (α : Type _) [Fintype α] where
  mass : α → α → ℝ≥0
  total : ∀ x, ∑ y, mass x y = 1

def proposal (p : Proposal α) (x : α) : Measure α :=
  ∑ y, (p.mass x y : ℝ≥0∞) • dirac y

instance (p : Proposal α) (x : α) : IsProbabilityMeasure (proposal p x) where
  measure_univ := by
    simpa [proposal, ← ENNReal.ofNNReal_finsetSum] using
      congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (p.total x)

theorem proposal_singleton (p : Proposal α) (x y : α) :
    proposal p x {y} = (p.mass x y : ℝ≥0∞) := by
  classical
  simp [proposal, Pi.single_apply, eq_comm]

/-- A successful proposal moves; rejection keeps the current state. -/
def selection (w : α → ℝ≥0) (p : Proposal α) (x y : α) : Measure α :=
  (RealCoin.pmf (bias w p.mass x y) true • dirac y) +
    (RealCoin.pmf (bias w p.mass x y) false • dirac x)

instance (w : α → ℝ≥0) (p : Proposal α) (x y : α) :
    IsProbabilityMeasure (selection w p x y) where
  measure_univ := by simpa [selection] using RealCoin.pmf_sum (bias w p.mass x y)

/-- The standard Metropolis–Hastings transition kernel. -/
def kernel (w : α → ℝ≥0) (p : Proposal α) (x : α) : Measure α :=
  (proposal p x).bind (selection w p x)

instance (w : α → ℝ≥0) (p : Proposal α) (x : α) :
    IsProbabilityMeasure (kernel w p x) where
  measure_univ := by
    rw [kernel, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

/-- Away from the diagonal, only accepted proposals contribute. -/
theorem kernel_singleton_of_ne (w : α → ℝ≥0) (p : Proposal α) (x y : α) (h : x ≠ y) :
    kernel w p x {y} = RealCoin.pmf (bias w p.mass x y) true * (p.mass x y : ℝ≥0∞) := by
  classical
  rw [kernel, Measure.bind_apply (measurableSet_singleton y)
    (measurable_of_countable _).aemeasurable, lintegral_fintype]
  simp [selection, h, proposal_singleton, Pi.single_apply, eq_comm]

/-- Normalize the target weights. Zero-weight states remain outside its support. -/
def target (w : α → ℝ≥0) (_h : 0 < ∑ x, w x) : Measure α :=
  ((∑ x, w x : ℝ≥0) : ℝ≥0∞)⁻¹ • ∑ x, (w x : ℝ≥0∞) • dirac x

instance (w : α → ℝ≥0) (h : 0 < ∑ x, w x) : IsProbabilityMeasure (target w h) where
  measure_univ := by
    have hz : ((∑ x, w x : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h.ne'
    simp [target, ← ENNReal.ofNNReal_finsetSum, ENNReal.inv_mul_cancel hz]

theorem target_singleton (w : α → ℝ≥0) (h : 0 < ∑ x, w x) (y : α) :
    target w h {y} = (w y : ℝ≥0∞) / (∑ x, w x : ℝ≥0) := by
  classical
  simp [target, ENNReal.div_eq_inv_mul, smul_eq_mul, Pi.single_apply, eq_comm]

/-- Symmetric accepted flux is detailed balance for the normalized target. -/
theorem detailed_balance (w : α → ℝ≥0) (p : Proposal α) (h : 0 < ∑ x, w x) (x y : α) :
    (kernel w p x) {y} * (target w h) {x} =
      (kernel w p y) {x} * (target w h) {y} := by
  by_cases hxy : x = y
  · subst y
    rfl
  rw [kernel_singleton_of_ne w p x y hxy,
    kernel_singleton_of_ne w p y x (Ne.symm hxy), target_singleton, target_singleton]
  have hflux := congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞) / (∑ z, w z : ℝ≥0))
    (flux_symm w p.mass x y)
  simpa [RealCoin.pmf, bias, ENNReal.coe_mul, ENNReal.div_eq_inv_mul,
    mul_comm, mul_left_comm, mul_assoc] using hflux

/-- The Metropolis transition preserves its target; finite iteration preserves it too. -/
theorem invariant (w : α → ℝ≥0) (p : Proposal α) (h : 0 < ∑ x, w x) :
    (target w h).bind (kernel w p) = target w h :=
  FiniteKernels.invariant_of_detailed_balance _ _ (detailed_balance w p h)

end finite

end

end SampLib.Metropolis
