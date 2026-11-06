import SampLib.Discrete.Laws.Binomial
import SampLib.Common.Laws.BinomialMeasure

open MeasureTheory
open scoped ENNReal

namespace SampLib.Binomial

noncomputable section

private def mass (p : unitInterval) (n k : ℕ) : ℝ≥0∞ :=
  n.choose k * RealCoin.pmf p true ^ k * RealCoin.pmf p false ^ (n - k)

private theorem mass_succ (p : unitInterval) (n k : ℕ) :
    mass p (n + 1) (k + 1) =
      RealCoin.pmf p true * mass p n k + RealCoin.pmf p false * mass p n (k + 1) := by
  by_cases h : k < n
  · have hsub : n - k = n - (k + 1) + 1 := by omega
    simp only [mass, Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right]
    rw [hsub, pow_succ, pow_succ]
    ring
  · by_cases he : k = n
    · subst k
      simp [mass, pow_succ, mul_comm]
    · have hn : n < k := by omega
      simp [mass, Nat.choose_eq_zero_of_lt hn,
        Nat.choose_eq_zero_of_lt (by omega : n < k + 1),
        Nat.choose_eq_zero_of_lt (by omega : n + 1 < k + 1)]

/-- The independent-trial convolution has the usual binomial point masses. -/
theorem law_singleton (p : unitInterval) (n k : ℕ) :
    law p n {k} =
      (n.choose k : ℝ≥0∞) * RealCoin.pmf p true ^ k *
        RealCoin.pmf p false ^ (n - k) := by
  change law p n {k} = mass p n k
  induction n generalizing k with
  | zero => cases k <;> simp [law, mass]
  | succ n IH =>
    rw [law, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    cases k with
    | zero =>
      have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext i; simp
      rw [hpre]
      simp [IH, mass, pow_succ, mul_comm]
    | succ k =>
      have hpre : Nat.succ ⁻¹' ({k + 1} : Set ℕ) = {k} := by ext i; simp
      rw [hpre, IH, IH, mass_succ]
      rfl

/-- The convolution law agrees with mathlib's binomial distribution. -/
theorem law_eq_binomial (p : unitInterval) (n : ℕ) :
    law p n = ProbabilityTheory.binomial n p := by
  apply Measure.ext_of_singleton
  intro k
  rw [law_singleton, ProbabilityTheory.binomial_singleton]
  simp only [RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
  rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg p.2.1 _)),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow p.2.1, ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2)]

/-- The binomial expectation is a finite Bernstein-weighted sum. -/
theorem lintegral_eq_sum (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p n = ∑ k ∈ Finset.range (n + 1),
      ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) *
        F k := by
  rw [law_eq_binomial, ProbabilityTheory.binomial_eq_sum_dirac]
  simp [lintegral_finsetSum_measure, ← Nat.range_succ_eq_Iic]

end

end SampLib.Binomial
