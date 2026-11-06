module

public import SampLib.Distributions.Geometric
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! # A geometric number of alternating threshold refinements

`Sum.inr ()` represents an infinite run of successes. Keeping that outcome explicit
makes the first-failure decomposition valid at both endpoint probabilities.
-/

open MeasureTheory Measure
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.GeometricThreshold

noncomputable section

local instance : MeasurableSingletonClass (ℕ ⊕ Unit) where
  measurableSet_singleton k := by
    cases k with
    | inl n =>
      have h : MeasurableSet (Sum.inl '' ({n} : Set ℕ) : Set (ℕ ⊕ Unit)) :=
        (measurableSet_singleton n).inl_image
      simpa only [Set.image_singleton] using h
    | inr u =>
      have h : MeasurableSet (Sum.inr '' ({u} : Set Unit) : Set (ℕ ⊕ Unit)) :=
        (measurableSet_singleton u).inr_image
      simpa only [Set.image_singleton] using h

/-- Number of successes before the first failure, including the infinite run. -/
def failureLaw (q : unitInterval) : Measure (ℕ ⊕ Unit) :=
  if q = 1 then dirac (Sum.inr ()) else
    (ProbabilityTheory.geometricMeasure (unitInterval.symm q)).map Sum.inl

instance (q : unitInterval) : IsProbabilityMeasure (failureLaw q) := by
  unfold failureLaw
  split
  · infer_instance
  · constructor
    rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- One failed trial stops; a successful trial increments the remaining count. -/
theorem failure_expectation (q : unitInterval) (F : ℕ ⊕ Unit → ℝ≥0∞) :
    ∫⁻ k, F k ∂failureLaw q =
      ofReal (1 - (q : ℝ)) * F (Sum.inl 0) +
        ofReal q * ∫⁻ k, F (Sum.map Nat.succ id k) ∂failureLaw q := by
  by_cases hq : q = 1
  · subst q
    simp [failureLaw]
  · have hs : unitInterval.symm q ≠ 0 := unitInterval.symm_eq_zero.not.mpr hq
    simp only [failureLaw, ite_eq_right hq,
      lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    simpa only [unitInterval.coe_symm_eq, sub_sub_cancel, Sum.map_inl] using
      ProbabilityTheory.lintegral_geometricMeasure_succ (unitInterval.symm q) hs
        (fun n => F (Sum.inl n))

/-- A finite stopping count selects a partial sum; the infinite count selects its limit. -/
def threshold (s : ℕ → unitInterval) (limit : unitInterval) (n : ℕ) :
    ℕ ⊕ Unit → unitInterval
  | .inr _ => limit
  | .inl k => s (n + k)

/-- Continuation credit conditional on one fixed latent uniform point. -/
def credit (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval)
    (n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ k, (if u < (threshold s limit n k : ℝ) then F true else F false) ∂failureLaw q

/-- The independent first-failure law gives the callback's exact conditional split. -/
theorem credit_step (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval)
    (n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ) :
    credit q s limit n F u =
      ofReal (1 - (q : ℝ)) * (if u < (s n : ℝ) then F true else F false) +
        ofReal q * credit q s limit (n + 1) F u := by
  let K (t : unitInterval) : ℝ≥0∞ := if u < (t : ℝ) then F true else F false
  have hshift (k : ℕ ⊕ Unit) :
      threshold s limit n (Sum.map Nat.succ id k) = threshold s limit (n + 1) k := by
    cases k with
    | inl k => simp only [Sum.map_inl, threshold]; congr 1; omega
    | inr u => rfl
  have hfirst : K (threshold s limit n (Sum.inl 0)) = K (s n) :=
    congrArg K (by simp only [threshold, Nat.add_zero])
  have htail : (∫⁻ k, K (threshold s limit n (Sum.map Nat.succ id k)) ∂failureLaw q) =
      credit q s limit (n + 1) F u :=
    lintegral_congr (fun k => congrArg K (hshift k))
  exact (failure_expectation q (fun k => K (threshold s limit n k))).trans
    (by rw [hfirst, htail])

theorem measurable_credit (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval)
    (n : ℕ) (F : Bool → ℝ≥0∞) : Measurable (credit q s limit n F) := by
  unfold credit
  apply Measurable.lintegral_prod_right
  apply Measurable.ite
  · exact measurableSet_lt measurable_fst
      ((measurable_of_countable (fun k => (threshold s limit n k : ℝ))).comp measurable_snd)
  · exact measurable_const
  · exact measurable_const

/-- If every possible threshold exceeds the point, the conditional result is true. -/
theorem credit_true (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval)
    (n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ)
    (h : ∀ k, u < (threshold s limit n k : ℝ)) :
    credit q s limit n F u = F true := by
  simp only [credit, ite_eq_left (h _)]
  simp

/-- If no possible threshold exceeds the point, the conditional result is false. -/
theorem credit_false (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval)
    (n : ℕ) (F : Bool → ℝ≥0∞) (u : ℝ)
    (h : ∀ k, (threshold s limit n k : ℝ) ≤ u) :
    credit q s limit n F u = F false := by
  simp only [credit, ite_eq_right (not_lt.mpr (h _))]
  simp

/-- Every random threshold is bounded, so its scalar mean is an ordinary real integral. -/
theorem integrable_threshold (q : unitInterval) (s : ℕ → unitInterval)
    (limit : unitInterval) (n : ℕ) :
    Integrable (fun k => (threshold s limit n k : ℝ)) (failureLaw q) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun k => by
    rw [Real.norm_eq_abs, abs_of_nonneg (threshold s limit n k).2.1]
    exact (threshold s limit n k).2.2)

def mean (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval) (n : ℕ) : ℝ :=
  ∫ k, (threshold s limit n k : ℝ) ∂failureLaw q

theorem mean_mem (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval) (n : ℕ) :
    mean q s limit n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun k => (threshold s limit n k).2.1)
  · have h := integral_mono (integrable_threshold q s limit n) (integrable_const (1 : ℝ))
      (fun k => (threshold s limit n k).2.2)
    simpa [mean, measureReal_def] using h

def bias (q : unitInterval) (s : ℕ → unitInterval) (limit : unitInterval) (n : ℕ) :
    unitInterval := ⟨mean q s limit n, mean_mem q s limit n⟩

@[simp] theorem mean_one (s : ℕ → unitInterval) (limit : unitInterval) (n : ℕ) :
    mean 1 s limit n = limit := by simp [mean, failureLaw, threshold]

theorem mean_of_lt_one (q : unitInterval) (hq : q ≠ 1) (s : ℕ → unitInterval)
    (limit : unitInterval) (n : ℕ) :
    mean q s limit n =
      ∫ k, (s (n + k) : ℝ) ∂ProbabilityTheory.geometricMeasure (unitInterval.symm q) := by
  rw [mean, failureLaw, ite_eq_right hq,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

/-- The scalar threshold mean lifts to nonnegative expectations without restricting credits. -/
theorem lintegral_threshold (q : unitInterval) (s : ℕ → unitInterval)
    (limit : unitInterval) (n : ℕ) :
    (∫⁻ k, ofReal (threshold s limit n k) ∂failureLaw q) = ofReal (mean q s limit n) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_threshold q s limit n)
    (ae_of_all _ (fun k => (threshold s limit n k).2.1))).symm

theorem lintegral_complement (q : unitInterval) (s : ℕ → unitInterval)
    (limit : unitInterval) (n : ℕ) :
    (∫⁻ k, ofReal (1 - (threshold s limit n k : ℝ)) ∂failureLaw q) =
      ofReal (1 - mean q s limit n) := by
  have h := ofReal_integral_eq_lintegral_ofReal
    ((integrable_const (1 : ℝ)).sub (integrable_threshold q s limit n))
    (ae_of_all _ (fun k => sub_nonneg.mpr (threshold s limit n k).2.2))
  have hs := integral_sub (integrable_const (1 : ℝ)) (integrable_threshold q s limit n)
  simp only [Pi.sub_apply] at h hs
  rw [← h, hs]
  simp [mean, measureReal_def]

/-- Averaging Bernoulli thresholds produces a Bernoulli coin at their scalar mean. -/
theorem mixture_expectation (q : unitInterval) (s : ℕ → unitInterval)
    (limit : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) :
    (∫⁻ k, ofReal (threshold s limit n k) * F true +
      ofReal (1 - (threshold s limit n k : ℝ)) * F false ∂failureLaw q) =
        ofReal (mean q s limit n) * F true + ofReal (1 - mean q s limit n) * F false := by
  rw [lintegral_add_left (measurable_of_countable _) _,
    lintegral_mul_const (F true) (measurable_of_countable _),
    lintegral_mul_const (F false) (measurable_of_countable _),
    lintegral_threshold, lintegral_complement]

end

end SampLib.GeometricThreshold
