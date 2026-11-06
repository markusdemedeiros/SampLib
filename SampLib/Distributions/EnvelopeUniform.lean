module

public import SampLib.Distributions.EnvelopeFuture
public import SampLib.Distributions.DyadicPosterior

@[expose] public section

/-! # Uniform masses of resolved shadow intervals

Only the random interval endpoints are averaged. No fixed target is assumed to
lie inside an individual interval, and no subtraction of infinite credits occurs.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SampLib.EnvelopeFactory

noncomputable section

theorem uniform_lower_mass (L : ℝ) (hL : L ≤ 1) :
    DyadicPosterior.unitLaw (Iio L) = ENNReal.ofReal L := by
  rw [DyadicPosterior.unitLaw, Measure.restrict_apply measurableSet_Iio]
  have hset : Iio L ∩ Ico (0 : ℝ) 1 = Ico 0 L := by
    ext u
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨hu, h0, _⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, hu.trans_le hL⟩
  rw [hset]
  simp

theorem uniform_upper_mass (U : ℝ) (hU : 0 ≤ U) :
    DyadicPosterior.unitLaw (Ici U) = ENNReal.ofReal (1 - U) := by
  rw [DyadicPosterior.unitLaw, Measure.restrict_apply measurableSet_Ici]
  have hset : Ici U ∩ Ico (0 : ℝ) 1 = Ico U 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ici, mem_Ico]
    constructor
    · rintro ⟨hu, _, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, hU.trans hu, h1⟩
  rw [hset]
  simp

theorem uniform_band_mass (L U : ℝ) (hL : 0 ≤ L) (hU : U ≤ 1) :
    DyadicPosterior.unitLaw (Ico L U) = ENNReal.ofReal (U - L) := by
  rw [DyadicPosterior.unitLaw, Measure.restrict_apply measurableSet_Ico]
  have hset : Ico L U ∩ Ico (0 : ℝ) 1 = Ico L U := by
    exact inter_eq_left.mpr (Ico_subset_Ico hL hU)
  rw [hset]
  simp

theorem integral_resolvedCredit (L U : ℝ) (hL : 0 ≤ L) (hLU : L ≤ U) (hU : U ≤ 1)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ u, resolvedCredit L U u F ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal L * F true + ENNReal.ofReal (1 - U) * F false := by
  have hfun : (fun u => resolvedCredit L U u F) =
      (fun u => (Iio L).indicator (fun _ => F true) u +
        (Ici U).indicator (fun _ => F false) u) := by
    funext u
    by_cases hlo : u < L
    · have hhi : ¬U ≤ u := not_le.mpr (hlo.trans_le hLU)
      simp [resolvedCredit, indicator, hlo, hhi]
    · by_cases hhi : u < U
      · have hnot : ¬U ≤ u := not_le.mpr hhi
        simp [resolvedCredit, indicator, hlo, hhi, hnot]
      · have hUle : U ≤ u := le_of_not_gt hhi
        simp [resolvedCredit, indicator, hlo, hhi, hUle]
  rw [hfun, lintegral_add_left
    (f := (Iio L).indicator (fun _ => F true))
    (measurable_const.indicator measurableSet_Iio) _,
    lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ici]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [uniform_lower_mass L (hLU.trans hU), uniform_upper_mass U (hL.trans hLU)]
  ring

theorem integral_unresolvedIndicator (L U : ℝ) (hL : 0 ≤ L) (hU : U ≤ 1) :
    (∫⁻ u, unresolvedIndicator L U u ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (U - L) := by
  have hfun : unresolvedIndicator L U =
      (Ico L U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext u
    simp only [unresolvedIndicator, indicator, mem_Ico]
  rw [hfun, lintegral_indicator measurableSet_Ico]
  simpa using uniform_band_mass L U hL hU

end

end SampLib.EnvelopeFactory
