import SampLib.Weighted.Laws.CategoricalCDF
import SampLib.Common.Laws.IncompleteInformation

/-! # Real and integer inversion of a categorical CDF

Normalizing the integer prefixes gives the same categorical law whether the
inverse CDF is driven by a continuous unit uniform or a uniform integer rank.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.RealCategoricalCDF

noncomputable section

theorem prefix_le (ws : List ℕ) (k : ℕ) : (ws.take k).sum ≤ ws.sum := by
  have := List.sum_take_add_sum_drop ws k
  omega

/-- Prefix probabilities, including zero-weight plateaus. -/
def prefixProbability (ws : List ℕ) (ht : 0 < ws.sum) (x : ℤ) : unitInterval :=
  ⟨((ws.take (x + 1).toNat).sum : ℝ) / ws.sum,
    div_nonneg (by positivity) (by positivity),
    (div_le_one (by exact_mod_cast ht)).mpr (by exact_mod_cast prefix_le ws (x + 1).toNat)⟩

/-- The normalized categorical prefixes as a real finite CDF. -/
def model (ws : List ℕ) (ht : 0 < ws.sum) : IncompleteInformation.Model where
  size := ws.length
  positive := List.length_pos_of_sum_ne_zero ws ht.ne'
  cdf := prefixProbability ws ht
  monotone := by
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h := (CategoricalCDF.model ws ht).monotone hx hy hxy
    change ((ws.take (x + 1).toNat).sum : ℤ) ≤ (ws.take (y + 1).toNat).sum at h
    exact_mod_cast h
  upper_mass := by
    apply Subtype.ext
    change ((ws.take (((ws.length : ℤ) - 1 + 1).toNat)).sum : ℝ) / ws.sum = 1
    simp only [sub_add_cancel, Int.toNat_natCast, List.take_length]
    exact div_self (by exact_mod_cast ht.ne')

private theorem real_tail (ws : List ℕ) (ht : 0 < ws.sum) (x : ℤ)
    (hx : x < 0 ∨ (ws.length : ℤ) - 1 < x) :
    IncompleteInformation.law (model ws ht) (Iic x) = if x < 0 then 0 else 1 := by
  rw [IncompleteInformation.law,
    Measure.map_apply (IncompleteInformation.measurable_quantile _) measurableSet_Iic]
  rcases hx with hx | hx
  · have hempty : IncompleteInformation.quantile (model ws ht) ⁻¹' Iic x = ∅ := by
      ext u
      have h := (IncompleteInformation.quantile_range (model ws ht) u).1
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      omega
    rw [hempty, measure_empty, ite_eq_left hx]
  · have hfull : IncompleteInformation.quantile (model ws ht) ⁻¹' Iic x = univ := by
      ext u
      have h := (IncompleteInformation.quantile_range (model ws ht) u).2
      change IncompleteInformation.quantile (model ws ht) u ≤ (ws.length : ℤ) - 1 at h
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      omega
    have hlen := List.length_pos_of_sum_ne_zero ws ht.ne'
    rw [hfull, measure_univ, ite_eq_right (by omega)]

private theorem integer_tail (ws : List ℕ) (ht : 0 < ws.sum) (x : ℤ)
    (hx : x < 0 ∨ (ws.length : ℤ) - 1 < x) :
    FiniteCDF.law (CategoricalCDF.model ws ht) (Iic x) = if x < 0 then 0 else 1 := by
  let D := CategoricalCDF.model ws ht
  let : NeZero D.scale := ⟨D.positive.ne'⟩
  change InverseQuantile.law D.scale (FiniteCDF.quantile D) (Iic x) = _
  rw [InverseQuantile.law, Measure.map_apply (measurable_of_countable _) measurableSet_Iic]
  rcases hx with hx | hx
  · have hempty : FiniteCDF.quantile D ⁻¹' Iic x = ∅ := by
      ext i
      have h := (FiniteCDF.quantile_mem D i).1.1
      change (0 : ℤ) ≤ _ at h
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      omega
    rw [hempty, measure_empty, ite_eq_left hx]
  · have hfull : FiniteCDF.quantile D ⁻¹' Iic x = univ := by
      ext i
      have h := (FiniteCDF.quantile_mem D i).1.2
      change _ ≤ (ws.length : ℤ) - 1 at h
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      omega
    have hlen := List.length_pos_of_sum_ne_zero ws ht.ne'
    rw [hfull, measure_univ, ite_eq_right (by omega)]

/-- Continuous quantile inversion and integer-rank inversion define the same probability law. -/
theorem law_eq (ws : List ℕ) (ht : 0 < ws.sum) :
    IncompleteInformation.law (model ws ht) = CategoricalCDF.law ws := by
  rw [← CategoricalCDF.law_eq ws ht]
  apply Measure.ext_of_Iic
  intro x
  by_cases hx : x < 0 ∨ (ws.length : ℤ) - 1 < x
  · rw [real_tail ws ht x hx, integer_tail ws ht x hx]
  · have hgrid : x ∈ Icc 0 ((ws.length : ℤ) - 1) := by
      simp only [mem_Icc]
      omega
    rw [IncompleteInformation.cdf (model ws ht) x hgrid,
      FiniteCDF.cdf (CategoricalCDF.model ws ht) x hgrid]
    rfl

/-- Arbitrary continuation credits agree, including infinite credits. -/
theorem expectation (ws : List ℕ) (ht : 0 < ws.sum) (F : ℤ → ℝ≥0∞) :
    DyadicPosterior.credit [] (fun u => F (IncompleteInformation.quantile (model ws ht) u)) =
      ∫⁻ i, F i ∂CategoricalCDF.law ws := by
  rw [IncompleteInformation.expectation, law_eq]

end

end SampLib.RealCategoricalCDF
