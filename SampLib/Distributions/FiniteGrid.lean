import SampLib.Distributions.IntegerIntervals
import SampLib.Samplers.Choice

/-! # Finite positions for a uniform integer interval -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FiniteGrid

noncomputable section

/-- The integer represented by a finite grid position. -/
def point {width : ℕ} (lower : ℤ) (i : Fin width) : ℤ := lower + (i.val : ℤ)

/-- A total decoder; only its values inside the interval are used. -/
def position (lower : ℤ) (width : ℕ) [NeZero width] (z : ℤ) : Fin width :=
  Choice.position width (z - lower).toNat

def law (width : ℕ) : Measure (Fin width) := Measure.uniformOfFinset Finset.univ

instance (width : ℕ) [NeZero width] : IsProbabilityMeasure (law width) :=
  Measure.isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

theorem lower_lt_upper (lower : ℤ) (width : ℕ) [NeZero width] :
    lower < lower + (width : ℤ) := by
  have : (0 : ℤ) < width := by exact_mod_cast NeZero.pos width
  omega

theorem point_position (lower : ℤ) (width : ℕ) [NeZero width] (z : ℤ)
    (hz : z ∈ Set.Ico lower (lower + (width : ℤ))) :
    point lower (position lower width z) = z := by
  rcases hz with ⟨hzlo, hzhi⟩
  have hk : (z - lower).toNat < width := by omega
  simp only [position, Choice.position_of_lt _ hk, point]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- The uniform finite-grid credit is the arithmetic mean over positions. -/
theorem uniform_expectation (width : ℕ) (F : Fin width → ℝ≥0∞) :
    ∫⁻ i, F i ∂law width = (∑ i, F i) / width := by
  simp only [law, Measure.uniformOfFinset, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul]

theorem rank_expectation (width : ℕ) [NeZero width] (F : Fin width → ℝ≥0∞) :
    (∑ k ∈ Finset.range width, F (Choice.position width k)) / width =
      ∫⁻ i, F i ∂law width := by
  rw [uniform_expectation,
    ← Fin.sum_univ_eq_sum_range (fun k => F (Choice.position width k)) width]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- Translation and decoding transport the verified integer proposal to finite positions. -/
theorem range_expectation (lower : ℤ) (width : ℕ) [NeZero width]
    (F : Fin width → ℝ≥0∞) :
    ∫⁻ z, F (position lower width z)
      ∂RndIntExcRange.law lower (lower + (width : ℤ)) (lower_lt_upper lower width) =
      ∫⁻ i, F i ∂law width := by
  rw [RndIntExcRange.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [add_sub_cancel_left, Int.toNat_natCast]
  have hposition (k : ℕ) : position lower width (lower + (k : ℤ)) =
      Choice.position width k := by simp [position]
  simp_rw [hposition]
  rw [UniformInt.lintegral_law, rank_expectation]

end

end SampLib.FiniteGrid
