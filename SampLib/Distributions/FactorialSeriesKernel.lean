import SampLib.Distributions.FactorialSeriesState
import SampLib.Distributions.GeometricThreshold
import SampLib.Distributions.BoundsKernel

/-! # Conditional credits for factorial-series refinement

The stopping count is independent of the fixed latent uniform. Its geometric
memorylessness redistributes output credits; one fixed horizon band supplies
termination credit through every refinement of the same cached uniform.
-/

open Set Filter MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal Topology

namespace SampLib.FactorialSeries

noncomputable section

def meanBias (m : Mode) (p : unitInterval) : unitInterval :=
  GeometricThreshold.bias (callbackBias m p) (partialBias m) (limitBias m) 0

def continuation (m : Mode) (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  GeometricThreshold.credit (callbackBias m p) (partialBias m) (limitBias m) n F

def band (m : Mode) (N : ℕ) : Set ℝ := Ico (lower m N) (upper m N)

def horizonCredit (m : Mode) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  continuation m p n F u + (band m N).indicator (fun _ => 1) u

def failedCredit (m : Mode) (N n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  (if u < partialSum m n then F true else F false) + (band m N).indicator (fun _ => 1) u

def branchCredit (m : Mode) (p : unitInterval) (N n : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) :
    ℝ → ℝ≥0∞ := if b then horizonCredit m p N (n + 1) F else failedCredit m N n F

theorem measurable_continuation (m : Mode) (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) :
    Measurable (continuation m p n F) := GeometricThreshold.measurable_credit _ _ _ _ _

theorem measurable_horizonCredit (m : Mode) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) : Measurable (horizonCredit m p N n F) :=
  (measurable_continuation m p n F).add (measurable_const.indicator measurableSet_Ico)

theorem measurable_failedCredit (m : Mode) (N n : ℕ) (F : Bool → ℝ≥0∞) :
    Measurable (failedCredit m N n F) :=
  (Measurable.ite measurableSet_Iio measurable_const measurable_const).add
    (measurable_const.indicator measurableSet_Ico)

theorem measurable_branchCredit (m : Mode) (p : unitInterval) (N n : ℕ)
    (F : Bool → ℝ≥0∞) (b : Bool) : Measurable (branchCredit m p N n F b) := by
  cases b
  · exact measurable_failedCredit m N n F
  · exact measurable_horizonCredit m p N (n + 1) F

/-- Memorylessness splits the continuation; the unchanged horizon indicator is framed. -/
theorem expectation (m : Mode) (p : unitInterval) (q : List Bool) (N n : ℕ)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ b, DyadicPosterior.credit q (branchCredit m p N n F b)
      ∂RealCoin.law (callbackBias m p)) =
        DyadicPosterior.credit q (horizonCredit m p N n F) := by
  have hs := RealCoin.pmf_sum (callbackBias m p)
  simp only [RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false] at hs
  have hpoint (u : ℝ) :
      RealCoin.credit (callbackBias m p) (fun b => branchCredit m p N n F b u) =
        horizonCredit m p N n F u := by
    have hrec := GeometricThreshold.credit_step (callbackBias m p)
      (partialBias m) (limitBias m) n F u
    change continuation m p n F u =
      ofReal (1 - (callbackBias m p : ℝ)) *
        (if u < partialSum m n then F true else F false) +
          ofReal (callbackBias m p) * continuation m p (n + 1) F u at hrec
    simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false,
      branchCredit, horizonCredit, failedCredit]
    calc
      _ = (ofReal (1 - (callbackBias m p : ℝ)) *
            (if u < partialSum m n then F true else F false) +
          ofReal (callbackBias m p) * continuation m p (n + 1) F u) +
          (ofReal (callbackBias m p) + ofReal (1 - (callbackBias m p : ℝ))) *
            (band m N).indicator (fun _ => 1) u := by ring
      _ = _ := by rw [← hrec, hs, one_mul]
  simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, ite_true,
    Bool.false_eq_true, ite_false, DyadicPosterior.credit]
  rw [← lintegral_const_mul _ (measurable_branchCredit m p N n F true),
    ← lintegral_const_mul _ (measurable_branchCredit m p N n F false),
    ← lintegral_add_left
      (f := fun u : ℝ => ofReal (callbackBias m p) * branchCredit m p N n F true u)
      (measurable_const.mul (measurable_branchCredit m p N n F true)) _]
  exact lintegral_congr hpoint

/-- Averaging the independent random threshold recovers its Bernoulli mean. -/
theorem initial_continuation (m : Mode) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (continuation m p 0 F) = RealCoin.credit (meanBias m p) F := by
  let s := partialBias m
  let l := limitBias m
  let q := callbackBias m p
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
theorem threshold_bounds (m : Mode) (n : ℕ) (k : ℕ ⊕ Unit) :
    lower m n ≤ (GeometricThreshold.threshold (partialBias m) (limitBias m) n k : ℝ) ∧
      (GeometricThreshold.threshold (partialBias m) (limitBias m) n k : ℝ) ≤ upper m n := by
  cases k with
  | inl k =>
    exact AlternatingEnclosure.future_mem (coefficient m) (coefficient_anti m)
      (coefficient_nonneg m) n (n + k) (Nat.le_add_right n k)
  | inr u =>
    exact AlternatingEnclosure.limit_mem (coefficient m) (coefficient_anti m)
      (coefficient_nonneg m) (coefficient_summable m) n

/-- The unresolved band pays only its shrinking Lebesgue width initially. -/
theorem initial_expectation (m : Mode) (p : unitInterval) (N : ℕ) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (horizonCredit m p N 0 F) ≤
      RealCoin.credit (meanBias m p) F + ofReal (coefficient m N) := by
  rw [DyadicPosterior.credit]
  unfold horizonCredit
  rw [lintegral_add_left (measurable_continuation m p 0 F) _]
  unfold band
  rw [lintegral_indicator measurableSet_Ico]
  change DyadicPosterior.credit [] (continuation m p 0 F) + _ ≤ _
  rw [initial_continuation]
  apply add_le_add le_rfl
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul, DyadicPosterior.law_nil, DyadicPosterior.unitLaw]
  rw [Measure.restrict_apply measurableSet_Ico]
  calc
    volume (band m N ∩ Ico 0 1) ≤ volume (band m N) := measure_mono inter_subset_left
    _ = ofReal (coefficient m N) := by
      rw [band, Real.volume_Ico]
      exact congrArg ofReal (AlternatingEnclosure.width (coefficient m) N)

/-- One finite horizon suffices for any positive initial error-credit allowance. -/
theorem exists_horizon (m : Mode) (p : unitInterval) (F : Bool → ℝ≥0∞)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, DyadicPosterior.credit [] (horizonCredit m p (N + 1) 0 F) ≤
      RealCoin.credit (meanBias m p) F + δ := by
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 1) (by simp) hδ.ne'
  have ht : Tendsto (fun N : ℕ => coefficient m (N + 1)) atTop (𝓝 (0 : ℝ)) :=
    (coefficient_summable m).tendsto_atTop_zero.comp
      (tendsto_atTop_mono Nat.le_succ tendsto_id)
  have hs : ∀ᶠ N in Filter.atTop, coefficient m (N + 1) < (ε : ℝ) :=
    (tendsto_order.mp ht).2 _ (by exact_mod_cast hε)
  obtain ⟨N, hN⟩ := hs.exists
  refine ⟨N, (initial_expectation m p (N + 1) F).trans (add_le_add le_rfl ?_)⟩
  calc
    ofReal (coefficient m (N + 1)) ≤ ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hN.le
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    _ ≤ δ := le_of_lt (by simpa using hεδ)

theorem lower_credit (m : Mode) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q (lower m n) true) :
    F true ≤ DyadicPosterior.credit q (horizonCredit m p N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  refine hq.mono fun u hu => ?_
  have h := GeometricThreshold.credit_true (callbackBias m p) (partialBias m) (limitBias m)
    n F u (fun k => (of_decide_eq_true hu).trans_le (threshold_bounds m n k).1)
  change F true ≤ continuation m p n F u + _
  rw [continuation, h]
  exact le_add_of_nonneg_right zero_le

theorem upper_credit (m : Mode) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q (upper m n) false) :
    F false ≤ DyadicPosterior.credit q (horizonCredit m p N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  refine hq.mono fun u hu => ?_
  have h := GeometricThreshold.credit_false (callbackBias m p) (partialBias m) (limitBias m)
    n F u (fun k => (threshold_bounds m n k).2.trans (not_lt.mp (of_decide_eq_false hu)))
  change F false ≤ continuation m p n F u + _
  rw [continuation, h]
  exact le_add_of_nonneg_right zero_le

theorem failed_lower_credit (m : Mode) (N n : ℕ) (q : List Bool) (F : Bool → ℝ≥0∞)
    (hq : DyadicPosterior.resolves q (partialSum m n) true) :
    F true ≤ DyadicPosterior.credit q (failedCredit m N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by simp [failedCredit, of_decide_eq_true hu]

theorem failed_upper_credit (m : Mode) (N n : ℕ) (q : List Bool) (F : Bool → ℝ≥0∞)
    (hq : DyadicPosterior.resolves q (partialSum m n) false) :
    F false ≤ DyadicPosterior.credit q (failedCredit m N n F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by simp [failedCredit, of_decide_eq_false hu]

theorem resolved_conflict (q : List Bool) (t : ℝ)
    (h₀ : DyadicPosterior.resolves q t false) (h₁ : DyadicPosterior.resolves q t true) : False := by
  have h : ∀ᵐ u ∂DyadicPosterior.law q, False := by
    filter_upwards [h₀, h₁] with u hu₀ hu₁
    exact Bool.noConfusion (hu₀.symm.trans hu₁)
  exact h.exists.choose_spec

/-- Surviving to the chosen horizon makes the indicator a unit credit under the posterior. -/
theorem unresolved_credit (m : Mode) (p : unitInterval) (N : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hlo : DyadicPosterior.resolves q (lower m N) false)
    (hhi : DyadicPosterior.resolves q (upper m N) true) :
    1 ≤ DyadicPosterior.credit q (horizonCredit m p N N F) := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo, hhi] with u hlo hhi
  have hu : u ∈ band m N :=
    ⟨not_lt.mp (of_decide_eq_false hlo), of_decide_eq_true hhi⟩
  simp [horizonCredit, hu]

/-- Either callback outcome supplies the credit of a resolved lower answer. -/
theorem branch_lower_credit (m : Mode) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (b : Bool)
    (h : DyadicPosterior.resolves q
      ((nextLower m n b : ℝ) / stateDenominator m n) true) :
    F true ≤ DyadicPosterior.credit q (branchCredit m p N n F b) := by
  cases b
  · simp only [nextLower_false, failed_ratio] at h
    exact failed_lower_credit m N n q F h
  · simp only [nextLower_ratio] at h
    exact lower_credit m p N (n + 1) q F h

theorem branch_upper_credit (m : Mode) (p : unitInterval) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (b : Bool)
    (h : DyadicPosterior.resolves q
      ((nextUpper m n b : ℝ) / stateDenominator m n) false) :
    F false ≤ DyadicPosterior.credit q (branchCredit m p N n F b) := by
  cases b
  · simp only [nextUpper_false, failed_ratio] at h
    exact failed_upper_credit m N n q F h
  · simp only [nextUpper_ratio] at h
    exact upper_credit m p N (n + 1) q F h

/-- A retry certifies a successful callback group and the next deterministic band. -/
theorem retry_resolves (m : Mode) (n : ℕ) (q : List Bool) (b : Bool)
    (hlo : DyadicPosterior.resolves q
      ((nextLower m n b : ℝ) / stateDenominator m n) false)
    (hhi : DyadicPosterior.resolves q
      ((nextUpper m n b : ℝ) / stateDenominator m n) true) :
    b = true ∧ DyadicPosterior.resolves q (lower m (n + 1)) false ∧
      DyadicPosterior.resolves q (upper m (n + 1)) true := by
  cases b
  · simp only [nextLower_false, nextUpper_false, failed_ratio] at hlo hhi
    exact (resolved_conflict q (partialSum m n) hlo hhi).elim
  · exact ⟨rfl, by simpa only [nextLower_ratio] using hlo,
      by simpa only [nextUpper_ratio] using hhi⟩

end

end SampLib.FactorialSeries
