module

public import SampLib.Distributions.LatentReal.IntervalLimits

@[expose] public section

/-! # Adaptive precision schedules

Refinement may depend on the shared latent sample. The following facts apply
pointwise, so no independence between that sample and its schedule is assumed.
-/

open Filter Topology

namespace SampLib.LatentReal.RationalInterval.Approximates

variable {intervals : ℕ → RationalInterval} {x : ℝ}

/-- Asking for at least the requested precision retains convergence. -/
theorem refine (h : Approximates intervals x) (precision : ℕ → ℕ)
    (hprecision : ∀ n, n ≤ precision n) :
    Approximates (fun n => intervals (precision n)) x := by
  refine ⟨fun n => h.1 (precision n), ?_⟩
  exact h.2.comp (tendsto_atTop_mono hprecision tendsto_id)

/-- The reciprocal loop may increase precision until it separates from zero;
its output schedule still approximates the inverse of the same latent value. -/
theorem reciprocal_refine (h : Approximates intervals x) (hx : x ≠ 0)
    (precision : ℕ → ℕ) (hprecision : ∀ n, n ≤ precision n)
    (hzero : ∀ n, 0 < (intervals (precision n)).lower ∨ (intervals (precision n)).upper < 0) :
    Approximates (fun n => (intervals (precision n)).reciprocal (hzero n)) (1 / x) :=
  (h.refine precision hprecision).reciprocal hx hzero

end SampLib.LatentReal.RationalInterval.Approximates
