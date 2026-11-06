import SampLib.AbsorbingChain

/-! # The first stopping index of a nonhomogeneous Bernoulli sequence

The survival product telescopes against its one-step losses. Vanishing survival
normalizes the stopping law, including heavy-tailed laws of infinite mean.
-/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.AbsorbingChain

noncomputable section

/-- Mass of exiting after exactly `depth` continuations. -/
def mass (q : ℕ → ℝ≥0∞) (start depth : ℕ) : ℝ≥0∞ :=
  survival q start depth * (1 - q (start + depth))

@[simp] theorem mass_zero (q : ℕ → ℝ≥0∞) (start : ℕ) :
    mass q start 0 = 1 - q start := by simp [mass]

/-- Splitting off the first continuation shifts the stopping sequence. -/
theorem mass_succ (q : ℕ → ℝ≥0∞) (start depth : ℕ) :
    mass q start (depth + 1) = q start * mass q (start + 1) depth := by
  simp only [mass, survival_succ]
  rw [show start + (depth + 1) = start + 1 + depth by omega]
  ring

/-- Every finite prefix partitions unit mass into stopped and surviving paths. -/
theorem mass_partial_sum (q : ℕ → ℝ≥0∞) (hq : ∀ n, q n ≤ 1)
    (start depth : ℕ) :
    (∑ i ∈ Finset.range depth, mass q start i) + survival q start depth = 1 := by
  induction depth generalizing start with
  | zero => simp
  | succ depth ih =>
    rw [Finset.sum_range_succ', survival_succ, mass_zero]
    simp only [mass_succ]
    rw [← Finset.mul_sum]
    calc
      _ = (1 - q start) + q start *
          ((∑ i ∈ Finset.range depth, mass q (start + 1) i) +
            survival q (start + 1) depth) := by ring
      _ = 1 := by rw [ih]; simp [tsub_add_cancel_of_le (hq start)]

/-- Almost-sure absorption makes the total first-stop mass one. -/
theorem mass_sum (q : ℕ → ℝ≥0∞) (hq : ∀ n, q n ≤ 1) (start : ℕ)
    (absorbs : Filter.Tendsto (survival q start) Filter.atTop (nhds 0)) :
    ∑' depth, mass q start depth = 1 := by
  have h := (ENNReal.tendsto_nat_tsum (mass q start)).add absorbs
  simp only [add_zero] at h
  have hconst : (fun depth =>
      (∑ i ∈ Finset.range depth, mass q start i) + survival q start depth) =
      fun _ => (1 : ℝ≥0∞) := funext (mass_partial_sum q hq start)
  rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The actual stopping index, rather than the number of continuations. -/
def stopLaw (q : ℕ → ℝ≥0∞) (start : ℕ) : Measure ℕ :=
  Measure.sum (fun depth => mass q start depth • dirac (start + depth))

theorem isProbabilityMeasure_stopLaw (q : ℕ → ℝ≥0∞) (hq : ∀ n, q n ≤ 1)
    (start : ℕ) (absorbs : Filter.Tendsto (survival q start) Filter.atTop (nhds 0)) :
    IsProbabilityMeasure (stopLaw q start) where
  measure_univ := by simpa [stopLaw] using mass_sum q hq start absorbs

/-- Distinct depths correspond to distinct stopping indices. -/
theorem stopLaw_singleton (q : ℕ → ℝ≥0∞) (start depth : ℕ) :
    stopLaw q start {start + depth} = mass q start depth := by
  simp [stopLaw, Measure.sum_apply, Measure.smul_apply, smul_eq_mul,
    Pi.single_apply, Nat.add_left_cancel_iff]

/-- Expectations are summed over disjoint stopping depths. -/
theorem lintegral_stopLaw (q : ℕ → ℝ≥0∞) (start : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F n ∂stopLaw q start = ∑' depth, mass q start depth * F (start + depth) := by
  simp [stopLaw, lintegral_sum_measure, smul_eq_mul]

/-- First-step conditioning is the sole expectation identity used by the loop. -/
theorem stopLaw_expectation (q : ℕ → ℝ≥0∞) (start : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F n ∂stopLaw q start = (1 - q start) * F start +
      q start * ∫⁻ n, F n ∂stopLaw q (start + 1) := by
  rw [lintegral_stopLaw, lintegral_stopLaw,
    tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  simp only [mass_zero, Nat.add_zero]
  congr 1
  apply tsum_congr
  intro depth
  rw [mass_succ, show start + (depth + 1) = start + 1 + depth by omega]
  ring

end

end SampLib.AbsorbingChain
