import SampLib.Discrete.Laws.PoissonRational
import SampLib.Continuous.Laws.Rejection

/-! # Zero-truncated Poisson law

Conditioning a Poisson count to be positive is a rejection law. Conditioning
preserves output credit and pays for amplified zero-count retries.
-/

open scoped ENNReal NNReal

namespace SampLib.ZeroTruncatedPoisson

noncomputable section

open MeasureTheory

abbrev acceptance : Set ℕ := Set.Ioi 0

theorem acceptance_mass (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) acceptance ≠ 0 := by
  have hr : (0 : ℝ≥0) < PoissonRational.rate x y := by
    unfold PoissonRational.rate
    positivity
  have hr' : (0 : ℝ) < PoissonRational.rate x y := by exact_mod_cast hr
  have hpoint : 0 < ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) {1} := by
    rw [ProbabilityTheory.poissonMeasure_singleton]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  apply ne_of_gt
  apply lt_of_lt_of_le hpoint
  apply measure_mono
  intro n hn
  simp only [Set.mem_singleton_iff] at hn
  subst n
  decide

def law (x y : ℕ) (hx : 0 < x) (hy : 0 < y) : Measure ℕ :=
  Rejection.law (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy)

instance (x y : ℕ) (hx : 0 < x) (hy : 0 < y) : IsProbabilityMeasure (law x y hx hy) := by
  unfold law
  infer_instance

abbrev credit (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (F : ℕ → ℝ≥0∞) :=
  Rejection.credit (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy) F

def kernel (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :=
  Rejection.kernel (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy) F ε

theorem factor_gt_one (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    1 < Rejection.terminationFactor
      (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance := by
  exact lt_add_of_pos_right 1
    (ENNReal.toNNReal_pos (acceptance_mass x y hx hy) (measure_ne_top _ _))

/-- Conditioning preserves output credit and pays for amplified zero-count retries. -/
theorem expectation (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, kernel x y hx hy F ε n
      ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) ≤
      credit x y hx hy F + ε :=
  Rejection.expectation_preservation _ acceptance measurableSet_Ioi
    (acceptance_mass x y hx hy) F ε

end

end SampLib.ZeroTruncatedPoisson
