import SampLib.Weighted.Laws.WordRotation
import SampLib.Uniform.Laws.UniformInt

/-! # Expectation for the debiased modulo reduction

Complete rotated residue cycles preserve the output credit. The discarded prefix has less
than half the source mass, so it funds the retry with doubled credit.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.DebiasedModulo

noncomputable section

/-- A raw word pays its output on acceptance and the target plus doubled slack on
rejection. -/
def kernel (n width : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < width % n then (∫⁻ i, F i ∂UniformInt.law n) + 2 * ε else F (k % n)

/-- Complete residue cycles preserve output credit; the short prefix funds retries. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ k, kernel n width F ε k ∂UniformInt.law width ≤
      (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  let C := ∫⁻ i, F i ∂UniformInt.law n
  let q := width / n
  let t := width % n
  have hq : 0 < q := Nat.div_pos hnw hn
  have ht : t < n := Nat.mod_lt width hn
  have heq : t + n * q = width := Nat.mod_add_div width n
  have hnq : n ≤ n * q := by nlinarith
  have hwp : 0 < width := lt_of_lt_of_le hn hnw
  have hw : (width : ℝ≥0∞) ≠ 0 := by positivity
  have hwt : (width : ℝ≥0∞) ≠ ∞ := by finiteness
  have hsum : ∑ k ∈ range width, kernel n width F ε k =
      (t : ℝ≥0∞) * (C + 2 * ε) + q * ∑ j ∈ range n, F j := by
    rw [show range width = range (t + n * q) from congrArg range heq.symm,
      sum_range_add]
    have hprefix : ∑ k ∈ range t, kernel n width F ε k = t * (C + 2 * ε) := by
      simp only [kernel]
      rw [sum_congr rfl fun k hk => ite_eq_left (mem_range.mp hk)]
      simp [C, nsmul_eq_mul, mul_add]
    have hsuffix : ∑ k ∈ range (n * q), kernel n width F ε (t + k) =
        q * ∑ j ∈ range n, F j := by
      simp only [kernel, show ∀ k, ¬t + k < width % n from fun k => by omega,
        ite_false]
      exact WordRotation.sum_cycles n q t F
    rw [hprefix, hsuffix]
  have hcredit : (∑ j ∈ range n, F j) = n * C := by
    rw [show C = (∑ j ∈ range n, F j) / n from UniformInt.lintegral_law n F,
      ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  have hparts : ((t : ℝ≥0∞) + n * q) / width = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_add, heq, ENNReal.div_self hw hwt]
  have hretry : ((2 * t : ℕ) : ℝ≥0∞) / width ≤ 1 := by
    rw [ENNReal.div_le_iff hw hwt, one_mul]
    exact_mod_cast (show 2 * t ≤ width by omega)
  rw [UniformInt.lintegral_law]
  calc
    _ = (((t : ℝ≥0∞) + n * q) / width) * C +
        (((2 * t : ℕ) : ℝ≥0∞) / width) * ε := by
      rw [hsum, hcredit]
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hretry)

end

end SampLib.DebiasedModulo
