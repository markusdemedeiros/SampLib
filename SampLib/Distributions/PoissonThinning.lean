module

public import SampLib.Distributions.PoissonMeasure
public import SampLib.Distributions.BinomialMeasure

@[expose] public section

/-! # Independent thinning of a Poisson count -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.Distributions

noncomputable section

theorem poissonMeasure_zero : ProbabilityTheory.poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro k
  cases k <;> simp [ProbabilityTheory.poissonMeasure_singleton]

/-- Independent Poisson counts add their rates. -/
theorem lintegral_poisson_add (r t : ℝ≥0) (F : ℕ → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, F (x + y) ∂ProbabilityTheory.poissonMeasure t
      ∂ProbabilityTheory.poissonMeasure r) =
      ∫⁻ z, F z ∂ProbabilityTheory.poissonMeasure (r + t) := by
  rw [← ProbabilityTheory.poissonMeasure_conv_poissonMeasure,
    Measure.lintegral_conv (measurable_of_countable _)]

private theorem thinning_coefficient (r : ℝ≥0) (p : unitInterval) (k m : ℕ) :
    (Real.exp (-r) * (r : ℝ) ^ (k + m) / (k + m).factorial) *
        ((k + m).choose k * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ m) =
      (Real.exp (-r) * ((r : ℝ) * p) ^ k / k.factorial) *
        (((r : ℝ) * (1 - (p : ℝ))) ^ m / m.factorial) := by
  have hf : ((k + m).choose k : ℝ) * (k.factorial : ℝ) * m.factorial =
      ((k + m).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + m by omega)
    simp only [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  rw [← hf, pow_add, mul_pow, mul_pow]
  have hc : ((k + m).choose k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show k ≤ k + m by omega)
  field_simp

/-- A Poisson number of independent `p`-trials has Poisson rate `rp`. -/
theorem poissonMeasure_bind_binomial (r : ℝ≥0) (p : unitInterval) :
    (ProbabilityTheory.poissonMeasure r).bind (fun n => ProbabilityTheory.binomial n p) =
      ProbabilityTheory.poissonMeasure (r * unitInterval.toNNReal p) := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.bind_apply (measurableSet_singleton k)
    (measurable_of_countable _).aemeasurable, ProbabilityTheory.poissonMeasure,
    lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    ProbabilityTheory.binomial_singleton]
  have hinj : Function.Injective (fun m : ℕ => k + m) := by
    intro i j hij
    dsimp only at hij
    omega
  rw [← hinj.tsum_eq ?_]
  · have hp0 : 0 ≤ (p : ℝ) := p.2.1
    have hp1 : (p : ℝ) ≤ 1 := p.2.2
    let A : ℝ := Real.exp (-r) * ((r : ℝ) * p) ^ k / k.factorial
    let B : ℝ := (r : ℝ) * (1 - (p : ℝ))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := mul_nonneg r.2 (sub_nonneg.mpr hp1)
    have hs : HasSum (fun m : ℕ => A * (B ^ m / m.factorial)) (A * Real.exp B) := by
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp B).mul_left A
    have he : Real.exp (-r) * Real.exp B = Real.exp (-((r : ℝ) * p)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [B]
      ring
    calc
      _ = ∑' m : ℕ, ENNReal.ofReal (A * (B ^ m / m.factorial)) := by
        apply tsum_congr
        intro m
        rw [← ENNReal.ofReal_mul (by positivity :
          0 ≤ Real.exp (-r) * (r : ℝ) ^ (k + m) / (k + m).factorial)]
        rw [Nat.add_sub_cancel_left, thinning_coefficient]
      _ = ENNReal.ofReal (∑' m : ℕ, A * (B ^ m / m.factorial)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs.summable).symm
      _ = ENNReal.ofReal (A * Real.exp B) := by rw [hs.tsum_eq]
      _ = _ := by
        rw [ProbabilityTheory.poissonMeasure_singleton]
        simp only [NNReal.coe_mul, unitInterval.coe_toNNReal]
        congr 1
        dsimp [A]
        calc
          _ = (Real.exp (-r) * Real.exp B) * ((r : ℝ) * p) ^ k / k.factorial := by ring
          _ = _ := by rw [he]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    have hkn : k ≤ n := by
      by_contra h
      have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hz] at hn
    exact ⟨n - k, by dsimp only; omega⟩

end

end SampLib.Distributions
