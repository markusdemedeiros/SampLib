import SampLib.Bernoulli.Laws.AlternatingSeriesCredit

/-! # The mean bias of the alternating-series threshold

The mean bias averages the partial sums with geometric weights. It equals the sum of the
power series `∑ (-1)^n p^n a_n`, so a known sum of that series identifies the mean bias.
-/

open Set Filter MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal Topology

namespace SampLib.AlternatingSeries

noncomputable section

private theorem geometric_partial_mean (b : ℕ → ℝ) (q : unitInterval)
    (hq : (q : ℝ) < 1) (hb : Summable (fun n => ‖(q : ℝ) ^ n * b n‖)) :
    HasSum (fun n => (1 - (q : ℝ)) * q ^ n * ∑ j ∈ Finset.range (n + 1), b j)
      (∑' n, (q : ℝ) ^ n * b n) := by
  have hg := hasSum_geometric_of_lt_one q.2.1 hq
  have hgn : Summable (fun n : ℕ => ‖(q : ℝ) ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg q.2.1 _)] using hg.summable
  have hc := hasSum_sum_range_mul_of_summable_norm hb hgn
  rw [hg.tsum_eq] at hc
  have hconv (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1), ((q : ℝ) ^ j * b j) * q ^ (n - j)) =
        (q : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hjn]
  have h := hc.mul_left (1 - (q : ℝ))
  simp_rw [hconv] at h
  have he : (1 - (q : ℝ)) * ((∑' n, (q : ℝ) ^ n * b n) * (1 - (q : ℝ))⁻¹) =
      ∑' n, (q : ℝ) ^ n * b n := by
    field_simp [sub_ne_zero.mpr hq.ne']
  simpa only [he, mul_assoc] using h

/-- The full alternating power series converges sequentially to the output bias.
At `p=1` this is the alternating-series test; below one, Abel's finite-sum identity
is justified by a geometric bound on the weighted coefficients. -/
theorem weighted_partialSum_tendsto (a : Parameters) (p : unitInterval) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1),
      AlternatingEnclosure.sign n * (p : ℝ) ^ n * value a n)
      atTop (𝓝 (meanBias a p : ℝ)) := by
  by_cases hp : p = 1
  · subst p
    have h := partialSum_tendsto a
    change Tendsto (fun N => ∑ n ∈ Finset.range (N + 1),
      AlternatingEnclosure.sign n * value a n) atTop (𝓝 (limit a)) at h
    simpa only [meanBias, GeometricThreshold.bias, GeometricThreshold.mean_one,
      limitBias, Set.Icc.coe_one, one_pow, mul_one] using h
  · have hp1 : (p : ℝ) < 1 := lt_of_le_of_ne p.2.2 (fun h => hp (Subtype.ext h))
    have hsymm : unitInterval.symm p ≠ 0 := by
      intro h
      have := congrArg (fun a : unitInterval => (a : ℝ)) h
      simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero] at this
      linarith
    have hb : Summable (fun n => ‖(p : ℝ) ^ n *
        (AlternatingEnclosure.sign n * value a n)‖) := by
      apply (summable_geometric_of_lt_one p.2.1 hp1).of_nonneg_of_le (fun _ => norm_nonneg _)
      intro n
      have hv : value a n ≤ 1 := by
        have hi : value a 0 ≤ 1 := by
          change (a.coefficient 0 : ℝ) ≤ 1
          exact_mod_cast a.initial
        exact (value_decreasing a (Nat.zero_le n)).trans hi
      have hsign : ‖AlternatingEnclosure.sign n‖ = 1 := by
        unfold AlternatingEnclosure.sign
        split_ifs <;> norm_num
      rw [norm_mul, norm_mul, hsign, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg p.2.1 n), Real.norm_eq_abs,
        abs_of_nonneg (value_nonnegative a n)]
      exact mul_le_of_le_one_right (pow_nonneg p.2.1 n) hv
    have hmean : (meanBias a p : ℝ) = ∑' n,
        (p : ℝ) ^ n * (AlternatingEnclosure.sign n * value a n) := by
      change GeometricThreshold.mean p (partialBias a) (limitBias a) 0 = _
      rw [GeometricThreshold.mean_of_lt_one _ hp,
        ProbabilityTheory.integral_geometricMeasure hsymm]
      calc
        _ = ∑' n, (1 - (p : ℝ)) * p ^ n *
            ∑ j ∈ Finset.range (n + 1), AlternatingEnclosure.sign j * value a j := by
          apply tsum_congr
          intro n
          simp only [unitInterval.coe_symm_eq, zero_add, smul_eq_mul,
            partialBias, partialSum, AlternatingEnclosure.partialSum]
          ring
        _ = _ := (geometric_partial_mean _ p hp1 hb).tsum_eq
    have hs := hb.of_norm.hasSum.tendsto_sum_nat.comp
      (tendsto_atTop_mono Nat.le_succ tendsto_id)
    rw [hmean]
    convert hs using 1
    ext N
    apply Finset.sum_congr rfl
    intro n _
    ring

/-- Any analytic identification of the sequential series identifies the sampler's bias. -/
theorem mean_eq_of_tendsto (a : Parameters) (p : unitInterval) (s : ℝ)
    (hs : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1),
      AlternatingEnclosure.sign n * (p : ℝ) ^ n * value a n) atTop (𝓝 s)) :
    (meanBias a p : ℝ) = s :=
  tendsto_nhds_unique (weighted_partialSum_tendsto a p) hs

/-- Absolutely convergent function-series identities are a convenient specialization. -/
theorem mean_eq_of_hasSum (a : Parameters) (p : unitInterval) (s : ℝ)
    (hs : HasSum (fun n => AlternatingEnclosure.sign n * (p : ℝ) ^ n * value a n) s) :
    (meanBias a p : ℝ) = s := by
  apply mean_eq_of_tendsto a p s
  simpa only [Function.comp_def, Nat.succ_eq_add_one] using
    hs.tendsto_sum_nat.comp (tendsto_atTop_mono Nat.le_succ tendsto_id)

end

end SampLib.AlternatingSeries
