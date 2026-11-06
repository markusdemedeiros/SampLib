import SampLib.Common.Laws.DyadicRefinement
import SampLib.Uniform.Laws.RealCoin

/-! # Finite-horizon credits for rational enclosures

One fixed uniform comparison determines the output. At any chosen horizon, add
one credit on that enclosure's uncertainty interval. Returning pays the correct
bit; reaching the horizon unresolved owns a contradictory credit of at least one.
The initial extra expectation is bounded by the enclosure width.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.DyadicPosterior

/-- An almost-everywhere lower bound becomes a lower bound on posterior credit. -/
theorem le_credit_of_ae (q : List Bool) (G : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ᵐ u ∂law q, c ≤ G u) : c ≤ credit q G := by
  calc
    _ = ∫⁻ _ : ℝ, c ∂law q := by simp
    _ ≤ _ := lintegral_mono_ae h

end SampLib.DyadicPosterior

namespace SampLib.FromBounds

noncomputable section

/-- A rational enclosure of the target probability, with a positive denominator. -/
structure Interval (p : unitInterval) where
  lower : ℤ
  upper : ℤ
  denominator : ℕ
  positive : 0 < denominator
  below : (lower : ℝ) ≤ (p : ℝ) * denominator
  above : (p : ℝ) * denominator ≤ upper

def Interval.left {p : unitInterval} (a : Interval p) : ℝ := a.lower / (a.denominator : ℝ)

def Interval.right {p : unitInterval} (a : Interval p) : ℝ := a.upper / (a.denominator : ℝ)

def Interval.width {p : unitInterval} (a : Interval p) : ℝ := a.right - a.left

def Interval.uncertain {p : unitInterval} (a : Interval p) : Set ℝ := Ico a.left a.right

theorem Interval.left_le {p : unitInterval} (a : Interval p) : a.left ≤ (p : ℝ) := by
  exact (div_le_iff₀ (by exact_mod_cast a.positive)).mpr a.below

theorem Interval.le_right {p : unitInterval} (a : Interval p) : (p : ℝ) ≤ a.right := by
  exact (le_div_iff₀ (by exact_mod_cast a.positive)).mpr a.above

/-- Output credit viewed as a function of the shared latent uniform. -/
def outputCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  if u < (p : ℝ) then F true else F false

/-- The extra unit is charged only when the chosen horizon remains unresolved. -/
def horizonCredit {p : unitInterval} (a : Interval p) (F : Bool → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  outputCredit p F u + a.uncertain.indicator (fun _ => 1) u

theorem measurable_outputCredit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    Measurable (outputCredit p F) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_horizonCredit {p : unitInterval} (a : Interval p) (F : Bool → ℝ≥0∞) :
    Measurable (horizonCredit a F) :=
  (measurable_outputCredit p F).add (measurable_const.indicator measurableSet_Ico)

/-- The shared unit uniform induces the target Bernoulli continuation credit. -/
theorem output_expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (outputCredit p F) = RealCoin.credit p F := by
  rw [DyadicPosterior.credit, DyadicPosterior.law_nil]
  change (∫⁻ u, RealCoin.uniformCredit p F u ∂volume.restrict (Ico 0 1)) = _
  rw [restrict_Ico_eq_restrict_Icc]
  exact RealCoin.lintegral_uniformCredit p F

/-- The initial extra cost is at most the width of the chosen rational enclosure. -/
theorem initial_expectation {p : unitInterval} (a : Interval p) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (horizonCredit a F) ≤
      RealCoin.credit p F + ofReal a.width := by
  rw [DyadicPosterior.credit]
  unfold horizonCredit Interval.uncertain
  rw [lintegral_add_left (measurable_outputCredit p F),
    lintegral_indicator measurableSet_Ico]
  change DyadicPosterior.credit [] (outputCredit p F) + _ ≤ _
  rw [output_expectation]
  apply add_le_add le_rfl
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    one_mul, DyadicPosterior.law_nil]
  calc
    _ ≤ volume a.uncertain := Measure.restrict_apply_le _ _
    _ = _ := by simp [Interval.uncertain, Interval.width]

/-- Arbitrarily tight enclosures suffice; monotonicity and a convergence rate are unnecessary. -/
def Tight {p : unitInterval} (a : ℕ → Interval p) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n, (a n).width ≤ ε

/-- Any positive error budget pays for some finite uncertainty horizon. -/
theorem exists_horizon {p : unitInterval} (a : ℕ → Interval p) (ha : Tight a)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, DyadicPosterior.credit [] (horizonCredit (a N) F) ≤ RealCoin.credit p F + δ := by
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 1) (by simp) hδ.ne'
  obtain ⟨N, hN⟩ := ha ε (by exact_mod_cast hε)
  refine ⟨N, (initial_expectation (a N) F).trans (add_le_add le_rfl ?_)⟩
  calc
    ofReal (a N).width ≤ ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hN
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    _ ≤ δ := le_of_lt (by simpa using hεδ)

/-- A resolved lower comparison fixes the target bit throughout the posterior. -/
theorem lower_credit {p : unitInterval} (a h : Interval p) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q a.left true) :
    F true ≤ DyadicPosterior.credit q (horizonCredit h F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by
    have hu' : u < (p : ℝ) := (of_decide_eq_true hu).trans_le a.left_le
    simp [horizonCredit, outputCredit, hu']

/-- A resolved upper comparison fixes false throughout the posterior. -/
theorem upper_credit {p : unitInterval} (a h : Interval p) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hq : DyadicPosterior.resolves q a.right false) :
    F false ≤ DyadicPosterior.credit q (horizonCredit h F) := by
  apply DyadicPosterior.le_credit_of_ae
  exact hq.mono fun u hu => by
    have hu' : ¬u < (p : ℝ) := not_lt.mpr (a.le_right.trans (not_lt.mp (of_decide_eq_false hu)))
    simp [horizonCredit, outputCredit, hu']

/-- At the horizon, both unresolved comparisons certify ownership of at least one credit. -/
theorem unresolved_credit {p : unitInterval} (a : Interval p) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hlo : DyadicPosterior.resolves q a.left false)
    (hhi : DyadicPosterior.resolves q a.right true) :
    1 ≤ DyadicPosterior.credit q (horizonCredit a F) := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo, hhi] with u hlo hhi
  have hu : u ∈ a.uncertain :=
    ⟨not_lt.mp (of_decide_eq_false hlo), of_decide_eq_true hhi⟩
  simp [horizonCredit, hu]

end

end SampLib.FromBounds
