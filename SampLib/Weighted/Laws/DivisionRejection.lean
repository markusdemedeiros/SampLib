import SampLib.Common.Laws.WordIntervals
import SampLib.Common.Laws.UniformRejection
import SampLib.Uniform.Laws.UniformInt

/-! # Expectation for division with rejection

Full quotient blocks preserve the output credit. The incomplete last block holds at most
half the source words, so it funds the retry with doubled credit.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.DivisionRejection

noncomputable section

/-- A raw word pays its output on acceptance and the target plus doubled slack on
rejection. -/
def kernel (n width : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k / (width / n) < n then F (k / (width / n))
  else (∫⁻ i, F i ∂UniformInt.law n) + 2 * ε

/-- Full quotient blocks preserve output credit and finance doubled retry credit. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ k, kernel n width F ε k ∂UniformInt.law width ≤
      (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  let q := width / n
  have hq : 0 < q := Nat.div_pos hnw hn
  have ha : n * q ≤ width := Nat.mul_div_le width n
  have hr : width % n < n := Nat.mod_lt width hn
  have heq : width % n + n * q = width := Nat.mod_add_div width n
  have hnq : n ≤ n * q := by nlinarith
  have hhalf : width ≤ 2 * (n * q) := by omega
  have hcredit := WordIntervals.quotient_expectation q n hq F
  rw [Nat.mul_comm q n] at hcredit
  have hkernel : kernel n width F ε =
      UniformRejection.kernel (n * q) (fun k => F (k / q)) ε := by
    funext k
    simp only [kernel, UniformRejection.kernel, ← hcredit, q,
      Nat.div_lt_iff_lt_mul hq]
  rw [hkernel, UniformInt.lintegral_law]
  simpa only [hcredit] using UniformRejection.expectation (n * q) width
    (Nat.mul_pos hn hq) ha hhalf (fun k => F (k / q)) ε

end

end SampLib.DivisionRejection
