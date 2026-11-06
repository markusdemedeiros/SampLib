module

public import SampLib.Distributions.MultichooseSeries
public import SampLib.Distributions.AcceptedProposal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-! # Negative-binomial laws with positive real shape

The generalized binomial series normalizes the ascending-factorial mass. The
success endpoint `p=1` remains the point mass at zero.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.NegativeBinomialShape

noncomputable section

/-- The canonical failures-before-successes mass, allowing a real success shape. -/
def pmf (a : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ring.multichoose a n * (p : ℝ) ^ a * (1 - (p : ℝ)) ^ n)

def law (a : ℝ) (_ha : 0 < a) (p : unitInterval) (_hp : 0 < (p : ℝ)) : Measure ℕ :=
  Measure.count.withDensity (pmf a p)

instance (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ)) :
    IsProbabilityMeasure (law a ha p hp) where
  measure_univ := by
    rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact MultichooseSeries.tsum_pmf ha.le hp p.2.2

theorem law_singleton (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    law a ha p hp {n} = pmf a p n := by
  rw [law, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  simp

/-- Every nonnegative extended-real continuation is integrated by the canonical series. -/
theorem expectation (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, F n ∂law a ha p hp) = ∑' n, pmf a p n * F n := by
  rw [law, lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_count]
  rfl

theorem law_one (a : ℝ) (ha : 0 < a) : law a ha 1 (by norm_num) = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  cases n <;> simp [law_singleton, pmf]

theorem pmf_zero_shape (p : unitInterval) (n : ℕ) : pmf 0 p n = if n = 0 then 1 else 0 := by
  cases n <;> simp [pmf]

theorem pmf_zero_count (p : unitInterval) (r : ℕ) :
    pmf (r : ℝ) p 0 = ENNReal.ofReal (p : ℝ) ^ r := by
  simp only [pmf, Ring.multichoose_zero_right, pow_zero, one_mul, mul_one, Real.rpow_natCast]
  exact ENNReal.ofReal_pow p.2.1 r

/-- The mass recurrence agrees with the first-success/first-failure decomposition. -/
theorem pmf_pascal (p : unitInterval) (r n : ℕ) :
    pmf ((r + 1 : ℕ) : ℝ) p (n + 1) =
      ENNReal.ofReal (p : ℝ) * pmf (r : ℝ) p (n + 1) +
        ENNReal.ofReal (1 - (p : ℝ)) * pmf ((r + 1 : ℕ) : ℝ) p n := by
  have hreal :
      Ring.multichoose ((r : ℝ) + 1) (n + 1) * (p : ℝ) ^ (r + 1) * (1 - (p : ℝ)) ^ (n + 1) =
      (p : ℝ) * (Ring.multichoose (r : ℝ) (n + 1) * (p : ℝ) ^ r * (1 - (p : ℝ)) ^ (n + 1)) +
        (1 - (p : ℝ)) * (Ring.multichoose ((r : ℝ) + 1) n *
          (p : ℝ) ^ (r + 1) * (1 - (p : ℝ)) ^ n) := by
    rw [Ring.multichoose_succ_succ]
    simp only [pow_succ]
    ring
  have hleft : 0 ≤ (p : ℝ) *
      (Ring.multichoose (r : ℝ) (n + 1) * (p : ℝ) ^ r * (1 - (p : ℝ)) ^ (n + 1)) :=
    mul_nonneg p.2.1 (mul_nonneg (mul_nonneg (MultichooseSeries.nonneg (by positivity) _)
      (pow_nonneg p.2.1 _)) (pow_nonneg (sub_nonneg.mpr p.2.2) _))
  have hright : 0 ≤ (1 - (p : ℝ)) * (Ring.multichoose ((r : ℝ) + 1) n *
      (p : ℝ) ^ (r + 1) * (1 - (p : ℝ)) ^ n) :=
    mul_nonneg (sub_nonneg.mpr p.2.2)
      (mul_nonneg (mul_nonneg (MultichooseSeries.nonneg (by positivity) _)
        (pow_nonneg p.2.1 _)) (pow_nonneg (sub_nonneg.mpr p.2.2) _))
  simp only [pmf, Real.rpow_natCast]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hreal, ENNReal.ofReal_add hleft hright,
    ENNReal.ofReal_mul p.2.1, ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]

end

end SampLib.NegativeBinomialShape
