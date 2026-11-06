module

public import SampLib.Common.Laws.PoissonMeasure

@[expose] public section

/-! # The Poisson probability-generating function -/

open MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.Distributions

noncomputable section

/-- The exponential series evaluates the Poisson generating function. -/
theorem lintegral_poisson_pow (r : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∫⁻ n, ofReal (q ^ n) ∂ProbabilityTheory.poissonMeasure r =
      ofReal (Real.exp ((r : ℝ) * (q - 1))) := by
  let A : ℝ := Real.exp (-r)
  let B : ℝ := (r : ℝ) * q
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg r.2 hq
  have hs : HasSum (fun n : ℕ => A * (B ^ n / n.factorial)) (A * Real.exp B) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp B).mul_left A
  have he : A * Real.exp B = Real.exp ((r : ℝ) * (q - 1)) := by
    rw [show A = Real.exp (-r) from rfl, ← Real.exp_add]
    congr 1
    dsimp [B]
    ring
  rw [ProbabilityTheory.poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← he, ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hA (div_nonneg
      (pow_nonneg hB _) (Nat.cast_nonneg _))) hs.summable]
  apply tsum_congr
  intro n
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-r) * (r : ℝ) ^ n / n.factorial)]
  congr 1
  dsimp [A, B]
  rw [mul_pow]
  ring

end

end SampLib.Distributions
