import SampLib.Bernoulli.Laws.AlternatingSeries

/-! # Credits of the alternating-series threshold

A first failed callback freezes the alternating partial sum. If every callback succeeds, the
threshold is the alternating-series limit. Conditional credits keep the same latent uniform
throughout refinement.
-/

open Set Filter MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal Topology

namespace SampLib.AlternatingSeries

noncomputable section

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

end

end SampLib.AlternatingSeries
