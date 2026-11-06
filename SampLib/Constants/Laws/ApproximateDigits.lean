import SampLib.Constants.Laws.RadixPosterior
import SampLib.Common.Laws.BoundsKernel

/-! # Certified approximate radix digits

An unresolved prefix lies in the two cells next to the current approximation.
Choose one finite horizon at which their total width fits the error allowance.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace SampLib.FromApproximateDigits

noncomputable section

/-- The nth certificate describes source position `n+1`, to absolute integer error one. -/
structure Model where
  base : ℕ
  atLeastTwo : 1 < base
  probability : unitInterval
  approximation : ℕ → ℤ
  accurate : ∀ n, |(approximation n : ℝ) - (probability : ℝ) * (base : ℝ) ^ (n + 1)| ≤ 1

theorem Model.base_pos (D : Model) : 0 < D.base :=
  lt_trans Nat.zero_lt_one D.atLeastTwo

def Model.enclosure (D : Model) (n : ℕ) : FromBounds.Interval D.probability where
  lower := D.approximation n - 1
  upper := D.approximation n + 1
  denominator := D.base ^ (n + 1)
  positive := pow_pos D.base_pos _
  below := by
    have h := (abs_le.mp (D.accurate n)).2
    simp only [Int.cast_sub, Int.cast_one, Nat.cast_pow]
    linarith
  above := by
    have h := (abs_le.mp (D.accurate n)).1
    simp only [Int.cast_add, Int.cast_one, Nat.cast_pow]
    linarith

theorem Model.enclosure_width (D : Model) (n : ℕ) :
    (D.enclosure n).width = 2 / (D.base : ℝ) ^ (n + 1) := by
  simp only [FromBounds.Interval.width, FromBounds.Interval.left, FromBounds.Interval.right,
    Model.enclosure, Int.cast_sub, Int.cast_add, Int.cast_one, Nat.cast_pow]
  ring

theorem Model.tight (D : Model) : FromBounds.Tight D.enclosure := by
  have hb : (1 : ℝ) < D.base := by exact_mod_cast D.atLeastTwo
  have hq0 : 0 ≤ (D.base : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hq1 : (D.base : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hb
  have hlim : Tendsto (fun n : ℕ => (2 / (D.base : ℝ)) * ((D.base : ℝ)⁻¹) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (2 / (D.base : ℝ))
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 ε hε).exists
  refine ⟨n, ?_⟩
  rw [D.enclosure_width]
  calc
    _ = (2 / (D.base : ℝ)) * ((D.base : ℝ)⁻¹) ^ n := by
      simp only [div_eq_mul_inv, pow_succ, mul_inv_rev, inv_pow]
      ring
    _ ≤ ε := hn.le

/-- One fixed uncertainty indicator is retained throughout every digit refinement. -/
def Model.credit (D : Model) (N : ℕ) (F : Bool → ℝ≥0∞) (n : ℕ) (c : ℤ) : ℝ≥0∞ :=
  RadixPosterior.credit (D.base ^ n) c (FromBounds.horizonCredit (D.enclosure N) F)

/-- The uniform digit partitions the current cell and preserves its full credit. -/
theorem Model.expectation (D : Model) (N : ℕ) (F : Bool → ℝ≥0∞) (n : ℕ) (c : ℤ) :
    (∑ v ∈ Finset.range D.base, D.credit N F (n + 1) (c * D.base + v)) / D.base =
      D.credit N F n c := by
  simp only [Model.credit, pow_succ]
  exact (RadixPosterior.credit_split _ (pow_pos D.base_pos _) _ D.base_pos c _
    (FromBounds.measurable_horizonCredit _ F)).symm

theorem Model.exists_horizon (D : Model) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, D.credit N F 0 0 ≤ RealCoin.credit D.probability F + δ := by
  obtain ⟨N, hN⟩ := FromBounds.exists_horizon D.enclosure D.tight F δ hδ
  refine ⟨N, ?_⟩
  simpa only [Model.credit, pow_zero, RadixPosterior.credit, RadixPosterior.law_one_zero,
    DyadicPosterior.credit, DyadicPosterior.law_nil] using hN

theorem Model.true_credit (D : Model) (N n : ℕ) (c : ℤ) (F : Bool → ℝ≥0∞)
    (hc : c ≤ D.approximation n - 2) : F true ≤ D.credit N F (n + 1) c := by
  apply RadixPosterior.le_credit_of_ae
  filter_upwards [RadixPosterior.ae_mem_cell _ (pow_pos D.base_pos _) c] with u hu
  have hnum : (c : ℝ) + 1 ≤ ((D.enclosure n).lower : ℝ) := by
    simp only [Model.enclosure, Int.cast_sub, Int.cast_one]
    have : (c : ℝ) ≤ (D.approximation n : ℝ) - 2 := by exact_mod_cast hc
    linarith
  have hup := div_le_div_of_nonneg_right hnum
    (show (0 : ℝ) ≤ ((D.base ^ (n + 1) : ℕ) : ℝ) by positivity)
  have hp : u < (D.probability : ℝ) := hu.2.trans_le (hup.trans (D.enclosure n).left_le)
  simp [FromBounds.horizonCredit, FromBounds.outputCredit, hp]

theorem Model.false_credit (D : Model) (N n : ℕ) (c : ℤ) (F : Bool → ℝ≥0∞)
    (hc : D.approximation n + 1 ≤ c) : F false ≤ D.credit N F (n + 1) c := by
  apply RadixPosterior.le_credit_of_ae
  filter_upwards [RadixPosterior.ae_mem_cell _ (pow_pos D.base_pos _) c] with u hu
  have hnum : ((D.enclosure n).upper : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast hc
  have hlo := div_le_div_of_nonneg_right hnum
    (show (0 : ℝ) ≤ ((D.base ^ (n + 1) : ℕ) : ℝ) by positivity)
  have hp : ¬u < (D.probability : ℝ) :=
    not_lt.mpr (((D.enclosure n).le_right.trans hlo).trans hu.1)
  simp [FromBounds.horizonCredit, FromBounds.outputCredit, hp]

/-- An unresolved horizon prefix is contained in the certified two-cell interval. -/
theorem Model.unresolved_credit (D : Model) (N : ℕ) (c : ℤ) (F : Bool → ℝ≥0∞)
    (hfalse : ¬D.approximation N + 1 ≤ c) (htrue : ¬c ≤ D.approximation N - 2) :
    1 ≤ D.credit N F (N + 1) c := by
  apply RadixPosterior.le_credit_of_ae
  filter_upwards [RadixPosterior.ae_mem_cell _ (pow_pos D.base_pos _) c] with u hu
  have hlow : ((D.enclosure N).lower : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast (show D.approximation N - 1 ≤ c by omega)
  have hhigh : (c : ℝ) + 1 ≤ ((D.enclosure N).upper : ℝ) := by
    have : (c : ℝ) ≤ (D.approximation N : ℝ) := by
      exact_mod_cast (show c ≤ D.approximation N by omega)
    simp only [Model.enclosure, Int.cast_add, Int.cast_one]
    linarith
  have hd : (0 : ℝ) ≤ ((D.base ^ (N + 1) : ℕ) : ℝ) := by positivity
  have hlo := div_le_div_of_nonneg_right hlow hd
  have hhi := div_le_div_of_nonneg_right hhigh hd
  have hmem : u ∈ (D.enclosure N).uncertain :=
    ⟨hlo.trans hu.1, hu.2.trans_le hhi⟩
  simp [FromBounds.horizonCredit, hmem]

end

end SampLib.FromApproximateDigits
