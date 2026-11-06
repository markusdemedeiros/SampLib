import SampLib.Bernoulli.Laws.FactorialSeriesKernel

/-! # Arbitrary decreasing rational alternating-series thresholds

A first failed callback freezes the alternating partial sum. If every callback
succeeds, the threshold is the sequential alternating-series limit. Conditional
credits retain the same latent uniform throughout refinement.
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

def continuation (a : Parameters) (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  GeometricThreshold.credit p (partialBias a) (limitBias a) n F

def band (a : Parameters) (N : ℕ) : Set ℝ := Ico (lower a N) (upper a N)

def horizonCredit (a : Parameters) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  continuation a p n F u + (band a N).indicator (fun _ => 1) u

def failedCredit (a : Parameters) (N n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  (if u < partialSum a n then F true else F false) + (band a N).indicator (fun _ => 1) u

def branchCredit (a : Parameters) (p : unitInterval) (N n : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) :
    ℝ → ℝ≥0∞ := if b then horizonCredit a p N (n + 1) F else failedCredit a N n F

theorem measurable_continuation (a : Parameters) (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) :
    Measurable (continuation a p n F) := GeometricThreshold.measurable_credit _ _ _ _ _

theorem measurable_horizonCredit (a : Parameters) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) : Measurable (horizonCredit a p N n F) :=
  (measurable_continuation a p n F).add (measurable_const.indicator measurableSet_Ico)

theorem measurable_failedCredit (a : Parameters) (N n : ℕ) (F : Bool → ℝ≥0∞) :
    Measurable (failedCredit a N n F) :=
  (Measurable.ite measurableSet_Iio measurable_const measurable_const).add
    (measurable_const.indicator measurableSet_Ico)

theorem measurable_branchCredit (a : Parameters) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) (b : Bool) : Measurable (branchCredit a p N n F b) := by
  cases b
  · exact measurable_failedCredit a N n F
  · exact measurable_horizonCredit a p N (n + 1) F

/-- Memorylessness splits the continuation; the unchanged horizon indicator is framed. -/
theorem expectation (a : Parameters) (p : unitInterval) (q : List Bool) (N n : ℕ)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ b, DyadicPosterior.credit q (branchCredit a p N n F b)
      ∂RealCoin.law p) =
        DyadicPosterior.credit q (horizonCredit a p N n F) := by
  have hs := RealCoin.pmf_sum p
  simp only [RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false] at hs
  have hpoint (u : ℝ) :
      RealCoin.credit p (fun b => branchCredit a p N n F b u) =
        horizonCredit a p N n F u := by
    have hrec := GeometricThreshold.credit_step p
      (partialBias a) (limitBias a) n F u
    change continuation a p n F u =
      ofReal (1 - (p : ℝ)) *
        (if u < partialSum a n then F true else F false) +
          ofReal p * continuation a p (n + 1) F u at hrec
    simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false,
      branchCredit, horizonCredit, failedCredit]
    calc
      _ = (ofReal (1 - (p : ℝ)) *
            (if u < partialSum a n then F true else F false) +
          ofReal p * continuation a p (n + 1) F u) +
          (ofReal p + ofReal (1 - (p : ℝ))) *
            (band a N).indicator (fun _ => 1) u := by ring
      _ = _ := by rw [← hrec, hs, one_mul]
  simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, ite_true,
    Bool.false_eq_true, ite_false, DyadicPosterior.credit]
  rw [← lintegral_const_mul _ (measurable_branchCredit a p N n F true),
    ← lintegral_const_mul _ (measurable_branchCredit a p N n F false),
    ← lintegral_add_left
      (f := fun u : ℝ => ofReal p * branchCredit a p N n F true u)
      (measurable_const.mul (measurable_branchCredit a p N n F true)) _]
  exact lintegral_congr hpoint

/-- Averaging the independent random threshold recovers its Bernoulli mean. -/
theorem initial_continuation (a : Parameters) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (continuation a p 0 F) = RealCoin.credit (meanBias a p) F := by
  let s := partialBias a
  let l := limitBias a
  let q := p
  have ht : Measurable (fun k : ℕ ⊕ Unit => (GeometricThreshold.threshold s l 0 k : ℝ)) :=
    measurable_fun_sum (measurable_of_countable _) measurable_const
  have hj : Measurable (fun z : ℝ × (ℕ ⊕ Unit) =>
      if z.1 < (GeometricThreshold.threshold s l 0 z.2 : ℝ) then F true else F false) :=
    Measurable.ite (measurableSet_lt measurable_fst (ht.comp measurable_snd))
      measurable_const measurable_const
  change (∫⁻ u, ∫⁻ k,
    (if u < (GeometricThreshold.threshold s l 0 k : ℝ) then F true else F false)
    ∂GeometricThreshold.failureLaw q ∂DyadicPosterior.law []) = _
  rw [lintegral_lintegral_swap hj.aemeasurable]
  calc
    _ = ∫⁻ k, RealCoin.credit (GeometricThreshold.threshold s l 0 k) F
        ∂GeometricThreshold.failureLaw q := by
      apply lintegral_congr
      intro k
      exact FromBounds.output_expectation (GeometricThreshold.threshold s l 0 k) F
    _ = _ := GeometricThreshold.mixture_expectation q s l 0 F

/-- All possible remaining stopping thresholds lie in the current deterministic band. -/
theorem threshold_bounds (a : Parameters) (n : ℕ) (k : ℕ ⊕ Unit) :
    lower a n ≤ (GeometricThreshold.threshold (partialBias a) (limitBias a) n k : ℝ) ∧
      (GeometricThreshold.threshold (partialBias a) (limitBias a) n k : ℝ) ≤ upper a n := by
  cases k with
  | inl k =>
    exact future_bounds a n (n + k) (Nat.le_add_right n k)
  | inr u =>
    exact limit_bounds a n

/-- The unresolved band pays only its shrinking Lebesgue width initially. -/
theorem initial_expectation (a : Parameters) (p : unitInterval) (N : ℕ) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (horizonCredit a p N 0 F) ≤
      RealCoin.credit (meanBias a p) F + ofReal (value a N) := by
  rw [DyadicPosterior.credit]
  unfold horizonCredit
  rw [lintegral_add_left (measurable_continuation a p 0 F) _]
  unfold band
  rw [lintegral_indicator measurableSet_Ico]
  change DyadicPosterior.credit [] (continuation a p 0 F) + _ ≤ _
  rw [initial_continuation]
  apply add_le_add le_rfl
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul, DyadicPosterior.law_nil, DyadicPosterior.unitLaw]
  rw [Measure.restrict_apply measurableSet_Ico]
  calc
    volume (band a N ∩ Ico 0 1) ≤ volume (band a N) := measure_mono inter_subset_left
    _ = ofReal (value a N) := by
      rw [band, Real.volume_Ico]
      exact congrArg ofReal (AlternatingEnclosure.width (value a) N)

/-- One finite horizon suffices for any positive initial error-credit allowance. -/
theorem exists_horizon (a : Parameters) (p : unitInterval) (F : Bool → ℝ≥0∞)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, DyadicPosterior.credit [] (horizonCredit a p (N + 1) 0 F) ≤
      RealCoin.credit (meanBias a p) F + δ := by
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 1) (by simp) hδ.ne'
  have ht : Tendsto (fun N : ℕ => value a (N + 1)) atTop (𝓝 (0 : ℝ)) :=
    a.vanishes.comp
      (tendsto_atTop_mono Nat.le_succ tendsto_id)
  have hs : ∀ᶠ N in Filter.atTop, value a (N + 1) < (ε : ℝ) :=
    (tendsto_order.mp ht).2 _ (by exact_mod_cast hε)
  obtain ⟨N, hN⟩ := hs.exists
  refine ⟨N, (initial_expectation a p (N + 1) F).trans (add_le_add le_rfl ?_)⟩
  calc
    ofReal (value a (N + 1)) ≤ ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hN.le
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    _ ≤ δ := le_of_lt (by simpa using hεδ)

theorem lower_credit (a : Parameters) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q (lower a n) true) :
    F true ≤ DyadicPosterior.credit q (horizonCredit a p N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  refine hq.mono fun u hu => ?_
  have h := GeometricThreshold.credit_true p (partialBias a) (limitBias a)
    n F u (fun k => (of_decide_eq_true hu).trans_le (threshold_bounds a n k).1)
  change F true ≤ continuation a p n F u + _
  rw [continuation, h]
  exact le_add_of_nonneg_right zero_le

theorem upper_credit (a : Parameters) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q (upper a n) false) :
    F false ≤ DyadicPosterior.credit q (horizonCredit a p N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  refine hq.mono fun u hu => ?_
  have h := GeometricThreshold.credit_false p (partialBias a) (limitBias a)
    n F u (fun k => (threshold_bounds a n k).2.trans (not_lt.mp (of_decide_eq_false hu)))
  change F false ≤ continuation a p n F u + _
  rw [continuation, h]
  exact le_add_of_nonneg_right zero_le

theorem failed_lower_credit (a : Parameters) (N n : ℕ) (q : List Bool) (F : Bool → ℝ≥0∞)
    (hq : DyadicPosterior.resolves q (partialSum a n) true) :
    F true ≤ DyadicPosterior.credit q (failedCredit a N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by simp [failedCredit, of_decide_eq_true hu]

theorem failed_upper_credit (a : Parameters) (N n : ℕ) (q : List Bool) (F : Bool → ℝ≥0∞)
    (hq : DyadicPosterior.resolves q (partialSum a n) false) :
    F false ≤ DyadicPosterior.credit q (failedCredit a N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by simp [failedCredit, of_decide_eq_false hu]

theorem resolved_conflict (q : List Bool) (t : ℝ)
    (h₀ : DyadicPosterior.resolves q t false) (h₁ : DyadicPosterior.resolves q t true) : False := by
  have h : ∀ᵐ u ∂DyadicPosterior.law q, False := by
    filter_upwards [h₀, h₁] with u hu₀ hu₁
    exact Bool.noConfusion (hu₀.symm.trans hu₁)
  exact h.exists.choose_spec

/-- Surviving to the chosen horizon makes the indicator a unit credit under the posterior. -/
theorem unresolved_credit (a : Parameters) (p : unitInterval) (N : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hlo : DyadicPosterior.resolves q (lower a N) false)
    (hhi : DyadicPosterior.resolves q (upper a N) true) :
    1 ≤ DyadicPosterior.credit q (horizonCredit a p N N F) := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo, hhi] with u hlo hhi
  have hu : u ∈ band a N :=
    ⟨not_lt.mp (of_decide_eq_false hlo), of_decide_eq_true hhi⟩
  simp [horizonCredit, hu]

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
