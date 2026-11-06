import SampLib.Samplers.UniformInt

/-! # Uniform words grouped into equal intervals

Consecutive blocks make the quotient uniform; complete residue cycles make the
remainder uniform. These statements include infinite continuation credits.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.WordIntervals

noncomputable section

/-- Flatten consecutive blocks without changing their finite sum. -/
theorem sum_blocks (width copies : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range (width * copies), F k =
      ∑ i ∈ range copies, ∑ j ∈ range width, F (width * i + j) := by
  induction copies with
  | zero => simp
  | succ copies ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- Every quotient occurs once for each possible within-block position. -/
theorem sum_quotients (width copies : ℕ) (hw : 0 < width) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range (width * copies), F (k / width) =
      width * ∑ i ∈ range copies, F i := by
  rw [sum_blocks]
  have hblocks (i : ℕ) :
      ∑ j ∈ range width, F ((width * i + j) / width) = width * F i := by
    calc
      _ = ∑ j ∈ range width, F i := sum_congr rfl fun j hj => by
        rw [Nat.mul_add_div hw, Nat.div_eq_of_lt (mem_range.mp hj), Nat.add_zero]
      _ = _ := by simp [nsmul_eq_mul]
  simp_rw [hblocks]
  rw [mul_sum]

/-- Every residue occurs once in each complete block. -/
theorem sum_remainders (width copies : ℕ) (F : ℕ → ℝ≥0∞) :
    ∑ k ∈ range (width * copies), F (k % width) =
      copies * ∑ j ∈ range width, F j := by
  rw [sum_blocks]
  have hblocks (i : ℕ) :
      ∑ j ∈ range width, F ((width * i + j) % width) = ∑ j ∈ range width, F j :=
    sum_congr rfl fun j hj => by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.mp hj)]
  simp_rw [hblocks]
  simp [nsmul_eq_mul]

/-- Quotienting a rectangular uniform word preserves the uniform block law. -/
theorem quotient_expectation (width copies : ℕ) (hw : 0 < width) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F (k / width) ∂UniformInt.law (width * copies) =
      ∫⁻ i, F i ∂UniformInt.law copies := by
  rw [UniformInt.lintegral_law, sum_quotients width copies hw,
    Nat.cast_mul, ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness),
    UniformInt.lintegral_law]

/-- A complete number of residue cycles preserves the uniform residue law. -/
theorem remainder_expectation (width copies : ℕ) (hc : 0 < copies) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F (k % width) ∂UniformInt.law (width * copies) =
      ∫⁻ i, F i ∂UniformInt.law width := by
  rw [UniformInt.lintegral_law, sum_remainders, Nat.cast_mul,
    mul_comm (copies : ℝ≥0∞), ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness),
    UniformInt.lintegral_law]

end

end SampLib.WordIntervals
