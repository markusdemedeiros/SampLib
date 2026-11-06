import SampLib.Discrete.Laws.NegativeBinomialShapeBase
import SampLib.Discrete.Laws.NegativeBinomial

/-! # The existing integer-shape proposal has the canonical multichoose masses

First-trial decomposition gives the same two-dimensional Pascal recurrence.
Induction on failures, then successes, identifies every singleton exactly.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.NegativeBinomialShape

noncomputable section

private theorem proposal_zero_step (p : unitInterval) (hp : 0 < (p : ℝ)) (r : ℕ) :
    NegativeBinomial.law p (r + 1) {0} =
      ENNReal.ofReal (p : ℝ) * NegativeBinomial.law p r {0} := by
  have h := NegativeBinomial.expectation_step p hp r
    (({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)))
  have hshift : (fun k : ℕ => ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) (k + 1)) =
      fun _ => 0 := by
    funext k
    simp
  simpa only [hshift, lintegral_zero, mul_zero, add_zero,
    lintegral_indicator_const (measurableSet_singleton _), one_mul,
    RealCoin.pmf, ite_true] using h

private theorem proposal_succ_step (p : unitInterval) (hp : 0 < (p : ℝ)) (r n : ℕ) :
    NegativeBinomial.law p (r + 1) {n + 1} =
      ENNReal.ofReal (p : ℝ) * NegativeBinomial.law p r {n + 1} +
        ENNReal.ofReal (1 - (p : ℝ)) * NegativeBinomial.law p (r + 1) {n} := by
  have h := NegativeBinomial.expectation_step p hp r
    (({n + 1} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)))
  have hshift : (fun k : ℕ => ({n + 1} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) (k + 1)) =
      ({n} : Set ℕ).indicator (fun _ => 1) := by
    funext k
    simp only [Set.indicator, mem_singleton_iff, Nat.add_left_inj]
  simpa only [hshift, lintegral_indicator_const (measurableSet_singleton _), one_mul,
    RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false] using h

/-- The convolution sampler's law agrees with the generalized mass at every integer shape. -/
theorem integer_singleton (p : unitInterval) (hp : 0 < (p : ℝ)) (r n : ℕ) :
    NegativeBinomial.law p r {n} = pmf (r : ℝ) p n := by
  induction n generalizing r with
  | zero =>
    induction r with
    | zero => simp [NegativeBinomial.law, pmf]
    | succ r ih =>
      rw [proposal_zero_step p hp r, ih, pmf_zero_count, pmf_zero_count, pow_succ]
      ring
  | succ n ih =>
    induction r with
    | zero => simp [NegativeBinomial.law, pmf]
    | succ r ihr =>
      rw [proposal_succ_step p hp r n, ihr, ih (r + 1)]
      exact (pmf_pascal p r n).symm

/-- The actual integer proposal can be used directly with the real-shape canonical law. -/
theorem integer_law_eq (p : unitInterval) (hp : 0 < (p : ℝ)) (M : ℕ) (hM : 0 < M) :
    NegativeBinomial.law p M = law (M : ℝ) (by exact_mod_cast hM) p hp := by
  apply Measure.ext_of_singleton
  intro n
  rw [integer_singleton p hp, law_singleton]

end

end SampLib.NegativeBinomialShape
