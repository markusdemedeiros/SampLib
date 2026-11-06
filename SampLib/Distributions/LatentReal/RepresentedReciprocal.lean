module

public import SampLib.Distributions.LatentReal.ReciprocalSelection
public import SampLib.Distributions.LatentReal.ComparisonUncertainty
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-! # The actual first-separated reciprocal representation

A total interval family supplies the inverse, with zero as the unused fallback.
Finite-horizon credits charge only worlds whose first separating precision lies
past that horizon. This tail vanishes without a uniform convergence rate.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SampLib.LatentReal.RepresentedReciprocal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Ω : Type*}

open ReciprocalSelection

def interval (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω) : RationalInterval :=
  let a := I (precision I n ω) ω
  if h : separated a then a.reciprocal h else RationalInterval.point 0 1 (by norm_num)

private theorem not_separated_of_contains_zero (a : RationalInterval) (ha : a.Contains 0) :
    ¬ separated a := by
  rintro (h | h)
  · have hpos : 0 < a.lowerReal := div_pos (by exact_mod_cast h) a.denominatorReal_pos
    exact (not_lt_of_ge ha.1) hpos
  · have hneg : a.upperReal < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast h) a.denominatorReal_pos
    exact (not_lt_of_ge ha.2) hneg

/-- Zero worlds have the totalized zero representation; nonzero worlds refine the true inverse. -/
theorem approximates (I : ℕ → Ω → RationalInterval) (ω : Ω) {x : ℝ}
    (h : RationalInterval.Approximates (fun n => I n ω) x) :
    RationalInterval.Approximates (fun n => interval I n ω) (1 / x) := by
  by_cases hx : x = 0
  · subst x
    have hnone n : ¬ separated (I (precision I n ω) ω) :=
      not_separated_of_contains_zero _ (h.1 _)
    have heq : (fun n => interval I n ω) = fun _ => RationalInterval.point 0 1 (by norm_num) := by
      funext n
      simp only [interval, dite_eq_right (hnone n)]
    rw [heq]
    refine ⟨?_, ?_⟩
    · intro n
      simp [RationalInterval.Contains, RationalInterval.lowerReal,
        RationalInterval.upperReal, RationalInterval.point]
    · simp [RationalInterval.width, RationalInterval.lowerReal,
        RationalInterval.upperReal, RationalInterval.point]
  · have hsep n := precision_separated_of_approximates I n ω h hx
    have heq : (fun n => interval I n ω) =
        fun n => (I (precision I n ω) ω).reciprocal (hsep n) := by
      funext n
      simp only [interval, dite_eq_left (hsep n)]
    rw [heq]
    exact h.reciprocal_refine hx (fun n => precision I n ω) (fun n => precision_ge I n ω) hsep

theorem not_zero_endpoints (a : RationalInterval) {x : ℝ} (hx : a.Contains x) (hne : x ≠ 0) :
    ¬ (a.lower = 0 ∧ a.upper = 0) := by
  rintro ⟨hl, hu⟩
  apply hne
  apply le_antisymm
  · simpa [RationalInterval.upperReal, hu] using hx.2
  · simpa [RationalInterval.lowerReal, hl] using hx.1

theorem next_le_precision (I : ℕ → Ω → RationalInterval) (start k : ℕ) (ω : Ω)
    (hbound : k ≤ precision I start ω) (hnot : ¬ separated (I k ω))
    (hsep : separated (I (precision I start ω) ω)) : k + 1 ≤ precision I start ω := by
  have hne : k ≠ precision I start ω := by
    intro heq
    exact hnot (heq.symm ▸ hsep)
  omega

variable [MeasurableSpace Ω]

/-- The same measurable lookup supplies every integer field of the returned interval. -/
theorem measurable_fields (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper))
    (hd : ∀ k, Measurable (fun ω => (I k ω).denominator)) (n : ℕ) :
    Measurable (fun ω => (interval I n ω).lower) ∧
      Measurable (fun ω => (interval I n ω).upper) ∧
      Measurable (fun ω => (interval I n ω).denominator) := by
  have hL := measurable_selected I hl hu (fun k ω => (I k ω).lower) hl n
  have hU := measurable_selected I hl hu (fun k ω => (I k ω).upper) hu n
  have hD := measurable_selected I hl hu (fun k ω => (I k ω).denominator) hd n
  have hs : MeasurableSet {ω | separated (I (precision I n ω) ω)} :=
    (measurableSet_lt measurable_const hL).union (measurableSet_lt hU measurable_const)
  have hlow : (fun ω => (interval I n ω).lower) =
      fun ω => if separated (I (precision I n ω) ω) then
        (I (precision I n ω) ω).denominator * (I (precision I n ω) ω).lower else 0 := by
    funext ω
    by_cases h : separated (I (precision I n ω) ω) <;>
      simp [interval, h, RationalInterval.reciprocal, RationalInterval.point]
  have hupp : (fun ω => (interval I n ω).upper) =
      fun ω => if separated (I (precision I n ω) ω) then
        (I (precision I n ω) ω).denominator * (I (precision I n ω) ω).upper else 0 := by
    funext ω
    by_cases h : separated (I (precision I n ω) ω) <;>
      simp [interval, h, RationalInterval.reciprocal, RationalInterval.point]
  have hden : (fun ω => (interval I n ω).denominator) =
      fun ω => if separated (I (precision I n ω) ω) then
        (I (precision I n ω) ω).lower * (I (precision I n ω) ω).upper else 1 := by
    funext ω
    by_cases h : separated (I (precision I n ω) ω) <;>
      simp [interval, h, RationalInterval.reciprocal, RationalInterval.point]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlow]
    exact (hD.mul hL).ite hs measurable_const
  · rw [hupp]
    exact (hD.mul hU).ite hs measurable_const
  · rw [hden]
    exact (hL.mul hU).ite hs measurable_const

theorem measurable_width (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper))
    (hd : ∀ k, Measurable (fun ω => (I k ω).denominator)) (n : ℕ) :
    Measurable (fun ω => (interval I n ω).width) := by
  obtain ⟨hL, hU, hD⟩ := measurable_fields I hl hu hd n
  have hc : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  exact ((hc.comp hU).div (hc.comp hD)).sub ((hc.comp hL).div (hc.comp hD))

/-- One unit is reserved only beyond the fixed refinement horizon. -/
def tail (I : ℕ → Ω → RationalInterval) (start N : ℕ) : Set Ω :=
  {ω | N < precision I start ω}

def horizonCredit (I : ℕ → Ω → RationalInterval) (start N : ℕ)
    (F : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  F ω + (tail I start N).indicator (fun _ => 1) ω

theorem measurableSet_tail (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start N : ℕ) :
    MeasurableSet (tail I start N) :=
  measurableSet_lt measurable_const (measurable_precision I hl hu start)

theorem measurable_horizonCredit (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start N : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) : Measurable (horizonCredit I start N F) :=
  hF.add (measurable_const.indicator (measurableSet_tail I hl hu start N))

/-- Refinement preserves arbitrary continuation credits and pays only the unresolved tail mass. -/
theorem expectation_preservation (μ : Measure Ω) (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start N : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, horizonCredit I start N F ω ∂μ) = (∫⁻ ω, F ω ∂μ) + μ (tail I start N) := by
  change (∫⁻ ω, F ω + (tail I start N).indicator (fun _ => 1) ω ∂μ) = _
  rw [lintegral_add_left hF,
    lintegral_indicator_const (measurableSet_tail I hl hu start N), one_mul]

theorem tail_mass_tendsto_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start : ℕ) :
    Tendsto (fun N => μ (tail I start N)) atTop (𝓝 0) := by
  have hm N : Measurable ((tail I start N).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_tail I hl hu start N)
  have hb N : (tail I start N).indicator (fun _ => (1 : ℝ≥0∞)) ≤ᵐ[μ] fun _ => 1 := by
    apply Eventually.of_forall
    intro ω
    by_cases h : ω ∈ tail I start N <;> simp [h]
  have ht : ∀ᵐ ω ∂μ, Tendsto (fun N =>
      (tail I start N).indicator (fun _ => (1 : ℝ≥0∞)) ω) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (precision I start ω)] with N hN
    simp [tail, not_lt.mpr hN]
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1) hm hb (by simp) ht
  simpa only [lintegral_indicator_const (measurableSet_tail I hl hu start _), one_mul,
    lintegral_zero] using h

theorem exists_horizon (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start : ℕ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) : ∃ N, start ≤ N ∧ μ (tail I start N) < δ :=
  ((eventually_ge_atTop start).and
    ((tail_mass_tendsto_zero μ I hl hu start).eventually_lt_const hδ)).exists

theorem output_credit_le (μ : Measure Ω) (I : ℕ → Ω → RationalInterval)
    (start N : ℕ) (F : Ω → ℝ≥0∞) :
    (∫⁻ ω, F ω ∂μ) ≤ ∫⁻ ω, horizonCredit I start N F ω ∂μ :=
  lintegral_mono (fun _ => le_add_of_nonneg_right bot_le)

theorem unresolved_credit (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : ℕ → Ω → RationalInterval) (start N : ℕ) (F : Ω → ℝ≥0∞)
    (h : ∀ᵐ ω ∂μ, N < precision I start ω) :
    1 ≤ ∫⁻ ω, horizonCredit I start N F ω ∂μ := by
  calc
    1 = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [h] with ω hω
      change 1 ≤ F ω + (tail I start N).indicator (fun _ => 1) ω
      rw [indicator_of_mem (show ω ∈ tail I start N from hω)]
      exact le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ F ω from bot_le)

theorem exists_credit_horizon (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (start : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N, start ≤ N ∧ (∫⁻ ω, horizonCredit I start N F ω ∂μ) ≤ (∫⁻ ω, F ω ∂μ) + δ := by
  obtain ⟨N, hN, hmass⟩ := exists_horizon μ I hl hu start hδ
  refine ⟨N, hN, ?_⟩
  rw [expectation_preservation μ I hl hu start N F hF]
  exact add_le_add le_rfl hmass.le

end

end SampLib.LatentReal.RepresentedReciprocal
