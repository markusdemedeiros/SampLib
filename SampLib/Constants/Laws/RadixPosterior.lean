import SampLib.Common.Laws.DyadicPosterior
import SampLib.Uniform.Laws.UniformInt

/-! # Uniform posteriors after radix digits

A prefix `c` with denominator `d` leaves a uniform point in `[c/d,(c+1)/d)`.
The next uniform digit splits that cell into equally weighted child cells.
-/

open Set MeasureTheory Finset
open scoped ENNReal

namespace SampLib.RadixPosterior

noncomputable section

def embed (d : ℕ) (c : ℤ) (u : ℝ) : ℝ := ((c : ℝ) + u) / d

theorem measurable_embed (d : ℕ) (c : ℤ) : Measurable (embed d c) := by
  unfold embed
  fun_prop

def law (d : ℕ) (c : ℤ) : Measure ℝ := DyadicPosterior.unitLaw.map (embed d c)

instance (d : ℕ) (c : ℤ) : IsProbabilityMeasure (law d c) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_embed d c) MeasurableSet.univ]
    simp

@[simp] theorem law_one_zero : law 1 0 = DyadicPosterior.unitLaw := by
  have he : embed 1 0 = fun u : ℝ => u := by funext u; simp [embed]
  rw [law, he, Measure.map_id']

def cell (d : ℕ) (c : ℤ) : Set ℝ := Ico ((c : ℝ) / d) (((c : ℝ) + 1) / d)

theorem law_eq_uniform (d : ℕ) (hd : 0 < d) (c : ℤ) :
    law d c = (d : ℝ≥0∞) • volume.restrict (cell d c) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : embed d c = fun u => (c : ℝ) / d + (d : ℝ)⁻¹ * u := by
    funext u
    simp only [embed, div_eq_mul_inv]
    ring
  rw [law, he, DyadicPosterior.map_unit_affine _ _ (inv_pos.mpr hdR)]
  have hi : (c : ℝ) / d + (d : ℝ)⁻¹ = ((c : ℝ) + 1) / d := by ring
  simp only [inv_inv, ENNReal.ofReal_natCast, hi, cell]

theorem ae_mem_cell (d : ℕ) (hd : 0 < d) (c : ℤ) :
    ∀ᵐ u ∂law d c, u ∈ cell d c := by
  rw [law_eq_uniform d hd c]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ico) _

def credit (d : ℕ) (c : ℤ) (F : ℝ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ u, F u ∂law d c

theorem le_credit_of_ae (d : ℕ) (c : ℤ) (F : ℝ → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ᵐ u ∂law d c, a ≤ F u) : a ≤ credit d c F := by
  calc
    _ = ∫⁻ _ : ℝ, a ∂law d c := by simp
    _ ≤ _ := lintegral_mono_ae h

private def digit (b v : ℕ) (u : ℝ) : ℝ := ((v : ℝ) + u) / b

private theorem measurable_digit (b v : ℕ) : Measurable (digit b v) := by
  unfold digit
  fun_prop

private theorem digit_law (b : ℕ) (hb : 0 < b) (v : ℕ) :
    DyadicPosterior.unitLaw.map (digit b v) =
      (b : ℝ≥0∞) • volume.restrict (Ico ((v : ℝ) / b) (((v + 1 : ℕ) : ℝ) / b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he : digit b v = fun u => (v : ℝ) / b + (b : ℝ)⁻¹ * u := by
    funext u
    simp only [digit, div_eq_mul_inv]
    ring
  rw [he, DyadicPosterior.map_unit_affine _ _ (inv_pos.mpr hbR)]
  have hi : (v : ℝ) / b + (b : ℝ)⁻¹ = ((v + 1 : ℕ) : ℝ) / b := by
    push_cast
    ring
  simp only [inv_inv, ENNReal.ofReal_natCast, hi]

private theorem grid_partition (a : ℕ → ℝ) (ha : Monotone a) (n : ℕ) :
    (∑ v ∈ range n, volume.restrict (Ico (a v) (a (v + 1)))) =
      volume.restrict (Ico (a 0) (a n)) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ, IH, ← Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
      Ico_union_Ico_eq_Ico (ha (Nat.zero_le n)) (ha (Nat.le_succ n))]

private theorem unit_split (b : ℕ) (hb : 0 < b) :
    DyadicPosterior.unitLaw = (b : ℝ≥0∞)⁻¹ •
      ∑ v ∈ range b, DyadicPosterior.unitLaw.map (digit b v) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsum : (∑ v ∈ range b, DyadicPosterior.unitLaw.map (digit b v)) =
      (b : ℝ≥0∞) • DyadicPosterior.unitLaw := by
    simp_rw [digit_law b hb]
    rw [← smul_sum, grid_partition (fun v : ℕ => (v : ℝ) / b)
      (fun i j hij => div_le_div_of_nonneg_right (by exact_mod_cast hij) hbR.le)]
    simp only [Nat.cast_zero, zero_div, div_self hbR.ne', DyadicPosterior.unitLaw]
  rw [hsum, smul_smul, ENNReal.inv_mul_cancel (by positivity : (b : ℝ≥0∞) ≠ 0)
    (by finiteness : (b : ℝ≥0∞) ≠ ∞), one_smul]

private theorem unit_expectation (b : ℕ) (hb : 0 < b) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ u, F u ∂DyadicPosterior.unitLaw =
      (∑ v ∈ range b, ∫⁻ u, F (digit b v u) ∂DyadicPosterior.unitLaw) / b := by
  conv_lhs => rw [unit_split b hb]
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_map hF (measurable_digit b _)]
  rw [smul_eq_mul, ENNReal.div_eq_inv_mul]

private theorem embed_digit (d : ℕ) (hd : 0 < d) (b : ℕ) (hb : 0 < b)
    (c : ℤ) (v : ℕ) (u : ℝ) :
    embed d c (digit b v u) = embed (d * b) (c * b + v) u := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [embed, digit, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp
  ring

/-- Averaging the next uniform digit preserves every measurable continuation credit. -/
theorem credit_split (d : ℕ) (hd : 0 < d) (b : ℕ) (hb : 0 < b) (c : ℤ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    credit d c F =
      (∑ v ∈ range b, credit (d * b) (c * b + v) F) / b := by
  calc
    _ = (∑ v ∈ range b, ∫⁻ u, F (embed d c (digit b v u))
        ∂DyadicPosterior.unitLaw) / b := by
      rw [credit, law, lintegral_map hF (measurable_embed d c)]
      exact unit_expectation b hb _ (hF.comp (measurable_embed d c))
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro v hv
      rw [credit, law, lintegral_map hF (measurable_embed _ _)]
      apply lintegral_congr
      intro u
      rw [embed_digit d hd b hb c v u]

end

end SampLib.RadixPosterior
