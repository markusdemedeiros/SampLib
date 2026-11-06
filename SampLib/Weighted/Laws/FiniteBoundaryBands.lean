import SampLib.Common.Laws.DyadicPosterior
import SampLib.Common.Laws.BitRecycler

/-! # Vanishing credit around finitely many classification boundaries -/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.FiniteBoundaryBands

noncomputable section

/-- An open error band around each boundary, with repetitions harmless. -/
def bands {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ) : Set ℝ :=
  ⋃ i, Ioo (boundary i - radius) (boundary i + radius)

theorem measurable_bands {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ) :
    MeasurableSet (bands boundary radius) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioo)

/-- A union bound pays at most one interval length per boundary. -/
theorem mass_bound {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ) :
    DyadicPosterior.unitLaw (bands boundary radius) ≤ (n : ℝ≥0∞) * ofReal (2 * radius) := by
  calc
    _ ≤ ∑' i, DyadicPosterior.unitLaw (Ioo (boundary i - radius) (boundary i + radius)) :=
      measure_iUnion_le _
    _ ≤ ∑' i : Fin n, volume (Ioo (boundary i - radius) (boundary i + radius)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact Measure.restrict_apply_le _ _
    _ = _ := by
      simp only [Real.volume_Ioo, show ∀ i : Fin n,
        boundary i + radius - (boundary i - radius) = 2 * radius by intro i; ring]
      simp [nsmul_eq_mul]

/-- One credit at the horizon rules out an unresolved classification. -/
def horizonCredit {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ) (G : ℝ → ℝ≥0∞)
    (u : ℝ) : ℝ≥0∞ :=
  G u + (bands boundary radius).indicator (fun _ => 1) u

theorem measurable_horizonCredit {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    Measurable (horizonCredit boundary radius G) :=
  hG.add (measurable_const.indicator (measurable_bands boundary radius))

/-- Initial auxiliary credit is bounded by the total boundary-band length. -/
theorem expectation_preservation {n : ℕ} (boundary : Fin n → ℝ) (radius : ℝ)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    DyadicPosterior.credit [] (horizonCredit boundary radius G) ≤
      DyadicPosterior.credit [] G + (n : ℝ≥0∞) * ofReal (2 * radius) := by
  unfold DyadicPosterior.credit horizonCredit
  rw [DyadicPosterior.law_nil, lintegral_add_left hG,
    lintegral_indicator (measurable_bands boundary radius)]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
  exact add_le_add le_rfl (mass_bound boundary radius)

/-- Uniform dyadic radii make the cutoff cost smaller than every positive error budget. -/
theorem exists_horizon (n : ℕ) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N : ℕ, (n : ℝ≥0∞) * ofReal (2 * (2 ^ N : ℝ)⁻¹) ≤ δ := by
  obtain ⟨N, hN⟩ := BitRecycler.exists_horizon (2 * n + 1) (by omega) δ hδ
  refine ⟨N, ?_⟩
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have heq : (n : ℝ≥0∞) * ofReal (2 * (2 ^ N : ℝ)⁻¹) =
      ((2 * n : ℕ) : ℝ≥0∞) / 2 ^ N := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hp]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_mul,
      Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
    ring
  rw [heq]
  simpa only [Nat.add_one_sub_one] using hN

end

end SampLib.FiniteBoundaryBands
