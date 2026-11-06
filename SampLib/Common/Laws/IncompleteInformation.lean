import SampLib.Common.Laws.RefinedComparison

/-! # Finite CDFs with arbitrary real masses

The first threshold above one shared uniform has exactly the supplied cumulative
probabilities. Its interval bracket is preserved by either bisection decision.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.IncompleteInformation

noncomputable section

/-- A finite CDF, with plateaus allowed and all mass reached at the final index. -/
structure Model where
  size : ℕ
  positive : 0 < size
  cdf : ℤ → unitInterval
  monotone : MonotoneOn cdf (Icc 0 ((size : ℤ) - 1))
  upper_mass : cdf ((size : ℤ) - 1) = 1

def Model.upper (D : Model) : ℤ := D.size - 1

private theorem upper_nonneg (D : Model) : 0 ≤ D.upper := by
  have := D.positive
  dsimp [Model.upper]
  omega

def candidates (D : Model) (u : ℝ) : Finset ℤ :=
  (Finset.Icc 0 D.upper).filter (fun x => u < (D.cdf x : ℝ))

private theorem candidates_nonempty (D : Model) {u : ℝ} (hu : u < 1) :
    (candidates D u).Nonempty := by
  refine ⟨D.upper, ?_⟩
  simp only [candidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨upper_nonneg D, le_rfl⟩, by simpa [Model.upper, D.upper_mass] using hu⟩

/-- First-reaching quantile, totalized at the upper endpoint outside uniform support. -/
def quantile (D : Model) (u : ℝ) : ℤ :=
  if h : u < 1 then (candidates D u).min' (candidates_nonempty D h) else D.upper

theorem quantile_mem (D : Model) {u : ℝ} (hu : u < 1) :
    quantile D u ∈ Icc 0 D.upper ∧ u < (D.cdf (quantile D u) : ℝ) := by
  have h := Finset.min'_mem (candidates D u) (candidates_nonempty D hu)
  simpa only [quantile, dite_eq_left hu, candidates, Finset.mem_filter, Finset.mem_Icc,
    Set.mem_Icc] using h

theorem quantile_range (D : Model) (u : ℝ) : quantile D u ∈ Icc 0 D.upper := by
  by_cases hu : u < 1
  · exact (quantile_mem D hu).1
  · simp [quantile, hu, upper_nonneg D]

/-- A threshold test is precisely the corresponding quantile-side test. -/
theorem quantile_le_iff (D : Model) {u : ℝ} (hu : u < 1) (x : ℤ)
    (hx : x ∈ Icc 0 D.upper) : quantile D u ≤ x ↔ u < (D.cdf x : ℝ) := by
  constructor
  · intro h
    exact (quantile_mem D hu).2.trans_le (D.monotone (quantile_mem D hu).1 hx h)
  · intro h
    rw [quantile, dite_eq_left hu]
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hx, h⟩

theorem monotone_quantile (D : Model) : Monotone (quantile D) := by
  intro u v huv
  by_cases hv : v < 1
  · exact (quantile_le_iff D (huv.trans_lt hv) _ (quantile_mem D hv).1).mpr
      (huv.trans_lt (quantile_mem D hv).2)
  · simpa only [quantile, dite_eq_right hv] using (quantile_range D u).2

theorem measurable_quantile (D : Model) : Measurable (quantile D) :=
  (monotone_quantile D).measurable

/-- Inversion of one ideal uniform gives the finite CDF's exact law. -/
def law (D : Model) : Measure ℤ := DyadicPosterior.unitLaw.map (quantile D)

instance (D : Model) : IsProbabilityMeasure (law D) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_quantile D) MeasurableSet.univ]
    simp

/-- Quantile inversion transports arbitrary, possibly infinite, continuation credits. -/
theorem expectation (D : Model) (F : ℤ → ℝ≥0∞) :
    DyadicPosterior.credit [] (fun u => F (quantile D u)) = ∫⁻ x, F x ∂law D := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_quantile D)]
  rw [DyadicPosterior.credit, DyadicPosterior.law_nil]

/-- The pushforward's cumulative mass is exactly the given real CDF. -/
theorem cdf (D : Model) (x : ℤ) (hx : x ∈ Icc 0 D.upper) :
    law D (Iic x) = ENNReal.ofReal (D.cdf x : ℝ) := by
  rw [law, Measure.map_apply (measurable_quantile D) measurableSet_Iic]
  have heq : DyadicPosterior.unitLaw ((quantile D) ⁻¹' Iic x) =
      DyadicPosterior.unitLaw (Iio (D.cdf x : ℝ)) := by
    apply measure_congr
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ico (0 : ℝ) 1)
      measurableSet_Ico] with u hu
    exact propext (quantile_le_iff D hu.2 x hx)
  rw [heq, DyadicPosterior.unitLaw, Measure.restrict_apply measurableSet_Iio,
    inter_comm, Ico_inter_Iio, min_eq_right (D.cdf x).property.2]
  simp

/-- A cached posterior is supported on one current quantile bracket. -/
def Bracket (D : Model) (q : List Bool) (lo hi : ℤ) : Prop :=
  0 ≤ lo ∧ hi ≤ D.upper ∧ lo ≤ hi ∧
    ∀ᵐ u ∂DyadicPosterior.law q, lo ≤ quantile D u ∧ quantile D u ≤ hi

namespace Bracket

theorem left_width (lo hi : ℤ) (h : lo < hi) :
    ((lo + hi) / 2 - lo).toNat < (hi - lo).toNat := by omega

theorem right_width (lo hi : ℤ) (h : lo < hi) :
    (hi - ((lo + hi) / 2 + 1)).toNat < (hi - lo).toNat := by omega

theorem initial (D : Model) (q : List Bool) : Bracket D q 0 D.upper :=
  ⟨le_rfl, le_rfl, upper_nonneg D, Filter.Eventually.of_forall (quantile_range D)⟩

theorem refines {D : Model} {q r : List Bool} {lo hi : ℤ}
    (h : Bracket D q lo hi) (hqr : q <+: r) : Bracket D r lo hi :=
  ⟨h.1, h.2.1, h.2.2.1, (DyadicPosterior.law_refines hqr).ae_le h.2.2.2⟩

theorem midpoint_mem {D : Model} {q : List Bool} {lo hi : ℤ}
    (h : Bracket D q lo hi) (hlt : lo < hi) :
    (lo + hi) / 2 ∈ Icc 0 D.upper := by
  have hmid : lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by omega
  exact ⟨h.1.trans hmid.1, hmid.2.le.trans h.2.1⟩

theorem left {D : Model} {q : List Bool} {lo hi : ℤ} (h : Bracket D q lo hi)
    (hlt : lo < hi) (hcmp : DyadicPosterior.resolves q (D.cdf ((lo + hi) / 2) : ℝ) true) :
    Bracket D q lo ((lo + hi) / 2) := by
  refine ⟨h.1, (midpoint_mem h hlt).2, by omega, ?_⟩
  filter_upwards [h.2.2.2, hcmp, DyadicPosterior.ae_mem_unit q] with u hu hc hun
  exact ⟨hu.1, (quantile_le_iff D hun.2 _ (midpoint_mem h hlt)).mpr
    (of_decide_eq_true hc)⟩

theorem right {D : Model} {q : List Bool} {lo hi : ℤ} (h : Bracket D q lo hi)
    (hlt : lo < hi) (hcmp : DyadicPosterior.resolves q (D.cdf ((lo + hi) / 2) : ℝ) false) :
    Bracket D q ((lo + hi) / 2 + 1) hi := by
  have hlo := h.1
  refine ⟨by omega, h.2.1, by omega, ?_⟩
  filter_upwards [h.2.2.2, hcmp, DyadicPosterior.ae_mem_unit q] with u hu hc hun
  have hnot : ¬quantile D u ≤ (lo + hi) / 2 := by
    rw [quantile_le_iff D hun.2 _ (midpoint_mem h hlt)]
    exact of_decide_eq_false hc
  exact ⟨by omega, hu.2⟩

theorem done_credit {D : Model} {q : List Bool} {lo : ℤ}
    (h : Bracket D q lo lo) (F : ℤ → ℝ≥0∞) :
    DyadicPosterior.credit q (fun u => F (quantile D u)) = F lo := by
  unfold DyadicPosterior.credit
  calc
    _ = ∫⁻ _ : ℝ, F lo ∂DyadicPosterior.law q := by
      apply lintegral_congr_ae
      exact h.2.2.2.mono fun _ hu => congrArg F (le_antisymm hu.2 hu.1)
    _ = _ := by simp

end Bracket

end

end SampLib.IncompleteInformation
