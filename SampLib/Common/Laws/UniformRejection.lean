import SampLib.Uniform.UniformInt

/-! # Credits for rejection from an enclosing uniform range

An enclosing range of at most twice the desired width leaves enough budget to
double auxiliary termination credit on every rejected word.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.UniformRejection

noncomputable section

/-- Accepted words keep their credit; rejected words restart with doubled slack. -/
def kernel (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < n then F k else (∫⁻ i, F i ∂UniformInt.law n) + 2 * ε

/-- The accepted interval is uniform and rejection uses at most half the range. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (hwidth : width ≤ 2 * n) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ k ∈ range width, kernel n F ε k) / width ≤
      (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  let C := ∫⁻ i, F i ∂UniformInt.law n
  have hwp : 0 < width := lt_of_lt_of_le hn hnw
  have hw : (width : ℝ≥0∞) ≠ 0 := by positivity
  have hwt : (width : ℝ≥0∞) ≠ ∞ := by finiteness
  have hsum : ∑ k ∈ range width, kernel n F ε k =
      (∑ k ∈ range n, F k) + (width - n : ℕ) * (C + 2 * ε) := by
    rw [← Nat.add_sub_of_le hnw, sum_range_add]
    have hfirst : ∑ k ∈ range n, kernel n F ε k = ∑ k ∈ range n, F k :=
      sum_congr rfl fun k hk => ite_eq_left (mem_range.mp hk)
    rw [hfirst]
    simp [kernel, Nat.not_lt.mpr (Nat.le_add_right n _), C, nsmul_eq_mul]
    ring
  have hcredit : (∑ k ∈ range n, F k) = (n : ℝ≥0∞) * C := by
    dsimp [C]
    rw [UniformInt.lintegral_law,
      ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  have hparts : ((n : ℝ≥0∞) + (width - n : ℕ)) / width = 1 := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hnw, ENNReal.div_self hw hwt]
  have hretry : ((2 * (width - n : ℕ) : ℕ) : ℝ≥0∞) / width ≤ 1 := by
    rw [ENNReal.div_le_iff hw hwt, one_mul]
    exact_mod_cast (show 2 * (width - n : ℕ) ≤ width by omega)
  calc
    _ = (((n : ℝ≥0∞) + (width - n : ℕ)) / width) * C +
        (((2 * (width - n : ℕ) : ℕ) : ℝ≥0∞) / width) * ε := by
      rw [hsum, hcredit]
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hretry)

end

end SampLib.UniformRejection
