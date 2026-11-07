import SampLib.Discrete.Laws.GaltonWatson
import SampLib.Discrete.Laws.PoissonRational

/-! # Borel law and its exploration kernel

The Borel law is the total progeny of a subcritical Poisson Galton–Watson tree.
Its branching identity preserves output credit, and the pending population pays
for termination.
-/

open scoped ENNReal NNReal

namespace SampLib.Borel

noncomputable section

open MeasureTheory

/-- The normalized total-progeny law in the subcritical regime. -/
def law (r : ℝ≥0) (_hr : r < 1) : Measure ℕ := GaltonWatson.law r

instance (r : ℝ≥0) (hr : r < 1) : IsProbabilityMeasure (law r hr) where
  measure_univ := GaltonWatson.law_mass r hr

def amplification (r : ℝ≥0) (hr : r < 1) : ℝ≥0 :=
  ⟨2 - r, by
    have h : (r : ℝ) < 1 := by exact_mod_cast hr
    linarith⟩

theorem amplification_gt_one (r : ℝ≥0) (hr : r < 1) : 1 < amplification r hr := by
  have h : (r : ℝ) < 1 := by exact_mod_cast hr
  change (1 : ℝ) < 2 - r
  linarith

private theorem amplification_add_rate (r : ℝ≥0) (hr : r < 1) :
    (amplification r hr : ℝ≥0∞) + r = 2 := by
  have h : amplification r hr + r = 2 := by
    apply NNReal.coe_injective
    change (2 - (r : ℝ)) + r = 2
    ring
  exact_mod_cast h

def budget (r : ℝ≥0) (pending population : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  GaltonWatson.credit r pending population F + ε * pending

def kernel (r : ℝ≥0) (hr : r < 1) (pending population : ℕ)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  budget r (pending + k) (population + 1) F ε + amplification r hr * ε

/-- Branching preserves the continuation, and the offspring mean exactly pays
for the amplified termination credit and the next pending population. -/
theorem expectation (r : ℝ≥0) (hr : r < 1) (pending population : ℕ)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, kernel r hr pending population F ε k ∂ProbabilityTheory.poissonMeasure r) =
      budget r (pending + 1) population F ε + ε := by
  simp only [kernel, budget, Nat.cast_add, Nat.cast_one, mul_add]
  rw [lintegral_add_left (measurable_of_countable _) _,
    lintegral_add_left (measurable_of_countable _) _,
    lintegral_add_left (measurable_of_countable _) _,
    lintegral_const_mul (f := fun k : ℕ => (k : ℝ≥0∞)) ε
      (measurable_of_countable _), GaltonWatson.poisson_mean,
    ← GaltonWatson.credit_recurrence]
  simp only [lintegral_const, measure_univ, mul_one]
  have h := amplification_add_rate r hr
  calc
    _ = GaltonWatson.credit r (pending + 1) population F +
        ε * pending + ε * ((amplification r hr : ℝ≥0∞) + r) := by ring
    _ = _ := by rw [h]; ring

theorem rate_lt_one (x y : ℕ) (hxy : x < y) : PoissonRational.rate x y < 1 := by
  unfold PoissonRational.rate
  exact (div_lt_one (by exact_mod_cast (Nat.zero_lt_of_lt hxy))).mpr (by exact_mod_cast hxy)

theorem termination_credit (δ : ℝ≥0∞) (hδ : 0 < δ) (pending : ℕ) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ δ = ε * pending + ε := by
  refine ⟨δ / (pending + 1), ENNReal.div_pos hδ.ne' (by finiteness), ?_⟩
  have h : δ / (pending + 1) * (pending + 1) = δ :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one] at h
  exact h.symm

end

end SampLib.Borel
