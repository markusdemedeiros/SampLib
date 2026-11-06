import SampLib.Bernoulli.Laws.AlternatingSeries

/-! # Uniform approximation of alternating-series factory probabilities

The enclosure width bounds the error uniformly over all input biases.
Finite polynomial approximants therefore give continuity even at p=1.
-/

open Set Filter
open scoped Topology

namespace SampLib.AlternatingSeries

noncomputable section

def polynomial (a : Parameters) (N : ℕ) (p : unitInterval) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), AlternatingEnclosure.sign n * (p : ℝ) ^ n * value a n

private theorem polynomial_error (a : Parameters) (N : ℕ) (p : unitInterval) :
    |polynomial a N p - (meanBias a p : ℝ)| ≤ value a N := by
  let s : ℕ → ℝ := fun n => (p : ℝ) ^ n * value a n
  have hs0 (n : ℕ) : 0 ≤ s n := mul_nonneg (pow_nonneg p.2.1 n) (value_nonnegative a n)
  have hs : Antitone s := by
    intro i j hij
    exact mul_le_mul (pow_le_pow_of_le_one p.2.1 p.2.2 hij) (value_decreasing a hij)
      (value_nonnegative a j) (pow_nonneg p.2.1 i)
  have ht : Tendsto (AlternatingEnclosure.partialSum s) atTop (𝓝 (meanBias a p : ℝ)) := by
    convert weighted_partialSum_tendsto a p using 1
    ext N
    simp only [AlternatingEnclosure.partialSum, s, mul_assoc]
  have hb : AlternatingEnclosure.lower s N ≤ (meanBias a p : ℝ) ∧
      (meanBias a p : ℝ) ≤ AlternatingEnclosure.upper s N := by
    constructor
    · apply ge_of_tendsto ht
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (AlternatingEnclosure.future_mem s hs hs0 N k hk).1
    · apply le_of_tendsto ht
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (AlternatingEnclosure.future_mem s hs hs0 N k hk).2
  have hp := AlternatingEnclosure.partial_mem s hs0 N
  have hw := AlternatingEnclosure.width s N
  have he : polynomial a N p = AlternatingEnclosure.partialSum s N := by
    simp only [polynomial, AlternatingEnclosure.partialSum, s, mul_assoc]
  rw [he]
  calc
    _ ≤ s N := by rw [abs_sub_le_iff]; constructor <;> linarith
    _ ≤ value a N := mul_le_of_le_one_left (value_nonnegative a N)
      (pow_le_one₀ p.2.1 p.2.2)

/-- The alternating remainder estimate is uniform over the closed unit interval. -/
theorem polynomial_tendstoUniformly (a : Parameters) :
    TendstoUniformly (polynomial a) (fun p : unitInterval => (meanBias a p : ℝ)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h := (tendsto_order.mp a.vanishes).2 ε hε
  filter_upwards [h] with N hN p
  rw [Real.dist_eq, abs_sub_comm]
  exact (polynomial_error a N p).trans_lt hN

/-- No absolute-summability premise is needed for continuity at deterministic input coins. -/
theorem continuous_meanBias (a : Parameters) :
    Continuous (fun p : unitInterval => (meanBias a p : ℝ)) := by
  apply (polynomial_tendstoUniformly a).continuous
  apply Filter.Eventually.frequently
  filter_upwards with N
  unfold polynomial
  fun_prop

end

end SampLib.AlternatingSeries
