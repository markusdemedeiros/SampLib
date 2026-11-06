import SampLib.Distributions.BoundsKernel

/-! # Conditional credits for progressively refined comparisons

A chosen horizon adds one credit on its unresolved interval. Its posterior cost
is at most the interval width divided by the cached dyadic cell's width.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.RefinedComparison

noncomputable section

/-- The continuation depends on the comparison result and on the same latent uniform. -/
def outputCredit (p : unitInterval) (G : Bool → ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  G (decide (u < (p : ℝ))) u

theorem outputCredit_ignore_result (p : unitInterval) (F : ℝ → ℝ≥0∞) :
    outputCredit p (fun _ => F) = F := rfl

/-- Seen without the latent state, a threshold comparison is the usual Bernoulli coin. -/
theorem constant_expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (outputCredit p (fun b _ => F b)) =
      RealCoin.credit p F := by
  convert FromBounds.output_expectation p F using 1
  congr 1
  funext u
  by_cases h : u < (p : ℝ) <;> simp [outputCredit, FromBounds.outputCredit, h]

/-- A comparison is a deterministic coin kernel, conditional on its latent uniform. -/
def threshold (p : unitInterval) (u : ℝ) : unitInterval :=
  if u < (p : ℝ) then 1 else 0

theorem measurable_threshold (p : unitInterval) : Measurable (threshold p) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- Only an unresolved comparison at the selected horizon consumes auxiliary credit. -/
def horizonCredit {p : unitInterval} (a : FromBounds.Interval p)
    (G : Bool → ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  outputCredit p G u + a.uncertain.indicator (fun _ => 1) u

theorem measurable_outputCredit (p : unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) : Measurable (outputCredit p G) := by
  have h : outputCredit p G = fun u => if u < (p : ℝ) then G true u else G false u := by
    funext u
    by_cases h : u < (p : ℝ) <;> simp [outputCredit, h]
  rw [h]
  exact Measurable.ite measurableSet_Iio (hG true) (hG false)

theorem measurable_horizonCredit {p : unitInterval} (a : FromBounds.Interval p)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    Measurable (horizonCredit a G) :=
  (measurable_outputCredit p G hG).add (measurable_const.indicator measurableSet_Ico)

/-- Conditional uncertainty scales by the inverse width of the already observed cell. -/
theorem expectation_preservation {p : unitInterval} (a : FromBounds.Interval p)
    (q : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    DyadicPosterior.credit q (horizonCredit a G) ≤
      DyadicPosterior.credit q (outputCredit p G) +
        ofReal (DyadicPosterior.width q)⁻¹ * ofReal a.width := by
  unfold DyadicPosterior.credit horizonCredit FromBounds.Interval.uncertain
  rw [lintegral_add_left (measurable_outputCredit p G hG),
    lintegral_indicator measurableSet_Ico]
  apply add_le_add le_rfl
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul, DyadicPosterior.law_eq_uniform, Measure.smul_apply, smul_eq_mul]
  gcongr
  calc
    _ ≤ volume a.uncertain := Measure.restrict_apply_le _ _
    _ = _ := by simp [FromBounds.Interval.uncertain, FromBounds.Interval.width]

/-- Arbitrarily tight intervals suffice for every cached posterior and positive error budget. -/
theorem exists_horizon {p : unitInterval} (a : ℕ → FromBounds.Interval p)
    (ha : FromBounds.Tight a) (q : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, DyadicPosterior.credit q (horizonCredit (a N) G) ≤
      DyadicPosterior.credit q (outputCredit p G) + δ := by
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := ofReal (DyadicPosterior.width q)⁻¹) ENNReal.ofReal_ne_top hδ.ne'
  obtain ⟨N, hN⟩ := ha ε (by exact_mod_cast hε)
  refine ⟨N, (expectation_preservation (a N) q G hG).trans (add_le_add le_rfl ?_)⟩
  calc
    _ ≤ ofReal (DyadicPosterior.width q)⁻¹ * ofReal (ε : ℝ) := by
      gcongr
    _ ≤ δ := le_of_lt (by simpa [mul_comm] using hεδ)

/-- A settled lower comparison determines the target comparison on the entire posterior. -/
theorem lower_resolves {p : unitInterval} (a : FromBounds.Interval p) (q : List Bool)
    (h : DyadicPosterior.resolves q a.left true) :
    DyadicPosterior.resolves q (p : ℝ) true :=
  h.mono fun _ hu => by simp [(of_decide_eq_true hu).trans_le a.left_le]

/-- A settled upper comparison determines the complementary target result. -/
theorem upper_resolves {p : unitInterval} (a : FromBounds.Interval p) (q : List Bool)
    (h : DyadicPosterior.resolves q a.right false) :
    DyadicPosterior.resolves q (p : ℝ) false :=
  h.mono fun _ hu => by
    simp [not_lt.mpr (a.le_right.trans (not_lt.mp (of_decide_eq_false hu)))]

/-- Settled branches retain their full latent-dependent continuation credit. -/
theorem return_credit {p : unitInterval} (a : FromBounds.Interval p) (q : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (b : Bool) (h : DyadicPosterior.resolves q (p : ℝ) b) :
    DyadicPosterior.credit q (G b) ≤ DyadicPosterior.credit q (horizonCredit a G) := by
  apply lintegral_mono_ae
  exact h.mono fun u hu => by simp [horizonCredit, outputCredit, hu]

/-- An unresolved horizon owns at least one credit, contradicting the credit invariant. -/
theorem unresolved_credit {p : unitInterval} (a : FromBounds.Interval p) (q : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (hlo : DyadicPosterior.resolves q a.left false)
    (hhi : DyadicPosterior.resolves q a.right true) :
    1 ≤ DyadicPosterior.credit q (horizonCredit a G) := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo, hhi] with u hlo hhi
  have hu : u ∈ a.uncertain :=
    ⟨not_lt.mp (of_decide_eq_false hlo), of_decide_eq_true hhi⟩
  simp [horizonCredit, hu]

end

end SampLib.RefinedComparison
