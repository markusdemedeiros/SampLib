import SampLib.Bernoulli.Laws.FactorialSeriesKernel

/-! # Arbitrary decreasing rational alternating-series thresholds

The parameters are decreasing rational coefficients that tend to zero. The alternating
partial sums converge to a limit in the unit interval and bracket it at every step.
-/

open Set Filter MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal Topology

namespace SampLib.AlternatingSeries

noncomputable section

/-- Source coefficients, allowing conditional rather than absolute convergence. -/
structure Parameters where
  coefficient : ℕ → ℚ
  nonnegative : ∀ n, 0 ≤ coefficient n
  decreasing : Antitone coefficient
  initial : coefficient 0 ≤ 1
  vanishes : Tendsto (fun n => (coefficient n : ℝ)) atTop (𝓝 0)

def value (a : Parameters) (n : ℕ) : ℝ := a.coefficient n

theorem value_nonnegative (a : Parameters) (n : ℕ) : 0 ≤ value a n := by
  change 0 ≤ (a.coefficient n : ℝ)
  exact_mod_cast a.nonnegative n

theorem value_decreasing (a : Parameters) : Antitone (value a) := by
  intro i j hij
  change (a.coefficient j : ℝ) ≤ (a.coefficient i : ℝ)
  exact_mod_cast a.decreasing hij

private theorem exists_limit (a : Parameters) :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * value a i) atTop (𝓝 l) :=
  (value_decreasing a).tendsto_alternating_series_of_tendsto_zero a.vanishes

/-- The ordinary sequential limit, including conditionally convergent series. -/
def limit (a : Parameters) : ℝ := Classical.choose (exists_limit a)

def partialSum (a : Parameters) := AlternatingEnclosure.partialSum (value a)

abbrev lower (a : Parameters) := AlternatingEnclosure.lower (value a)
abbrev upper (a : Parameters) := AlternatingEnclosure.upper (value a)

theorem partialSum_tendsto (a : Parameters) :
    Tendsto (partialSum a) atTop (𝓝 (limit a)) := by
  have h := (Classical.choose_spec (exists_limit a)).comp
    (tendsto_atTop_mono Nat.le_succ tendsto_id)
  change Tendsto (fun n => ∑ i ∈ Finset.range (n + 1),
    AlternatingEnclosure.sign i * value a i) atTop (𝓝 (limit a))
  simpa only [AlternatingEnclosure.sign_eq, Function.comp_def, limit,
    Nat.succ_eq_add_one] using h

theorem future_bounds (a : Parameters) (n k : ℕ) (hnk : n ≤ k) :
    lower a n ≤ partialSum a k ∧ partialSum a k ≤ upper a n :=
  AlternatingEnclosure.future_mem _ (value_decreasing a) (value_nonnegative a) n k hnk

theorem limit_bounds (a : Parameters) (n : ℕ) :
    lower a n ≤ limit a ∧ limit a ≤ upper a n := by
  constructor
  · apply ge_of_tendsto (partialSum_tendsto a)
    filter_upwards [eventually_ge_atTop n] with k hk using (future_bounds a n k hk).1
  · apply le_of_tendsto (partialSum_tendsto a)
    filter_upwards [eventually_ge_atTop n] with k hk using (future_bounds a n k hk).2

theorem partialSum_mem (a : Parameters) (n : ℕ) : partialSum a n ∈ Icc (0 : ℝ) 1 := by
  have h := future_bounds a 0 n (Nat.zero_le _)
  have hi : value a 0 ≤ 1 := by
    change (a.coefficient 0 : ℝ) ≤ 1
    exact_mod_cast a.initial
  simp only [lower, upper, AlternatingEnclosure.lower_zero,
    AlternatingEnclosure.upper_zero] at h
  exact ⟨h.1, h.2.trans hi⟩

theorem limit_mem (a : Parameters) : limit a ∈ Icc (0 : ℝ) 1 := by
  have h := limit_bounds a 0
  have hi : value a 0 ≤ 1 := by
    change (a.coefficient 0 : ℝ) ≤ 1
    exact_mod_cast a.initial
  simp only [lower, upper, AlternatingEnclosure.lower_zero,
    AlternatingEnclosure.upper_zero] at h
  exact ⟨h.1, h.2.trans hi⟩

def partialBias (a : Parameters) (n : ℕ) : unitInterval :=
  ⟨partialSum a n, partialSum_mem a n⟩

def limitBias (a : Parameters) : unitInterval := ⟨limit a, limit_mem a⟩

def meanBias (a : Parameters) (p : unitInterval) : unitInterval :=
  GeometricThreshold.bias p (partialBias a) (limitBias a) 0

end

end SampLib.AlternatingSeries
