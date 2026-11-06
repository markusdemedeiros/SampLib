import SampLib.Distributions.UniformRectangles
import SampLib.Distributions.UniformRejection

/-! # Credits for changing a uniform source modulus

Small targets retain complete residue blocks. Large targets recursively add a
low digit, giving an enclosing rectangle of less than twice the target width.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.ModulusReduction

noncomputable section

def limit (modulus n : ℕ) : ℕ := n * ((modulus - 1) / n)

def smallKernel (modulus n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  if r < n then F r else if r < limit modulus n then F (r % n)
  else (∫⁻ i, F i ∂UniformInt.law n) + 2 * ε

/-- Complete residue blocks conserve output credit; at most half the source is discarded. -/
theorem small_expectation (modulus n : ℕ) (hn : 0 < n) (hnm : n < modulus)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ r, smallKernel modulus n F ε r ∂UniformInt.law modulus ≤
      (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  let q := (modulus - 1) / n
  have hq : 0 < q := Nat.div_pos (by omega) hn
  have ha : n * q ≤ modulus - 1 := Nat.mul_div_le (modulus - 1) n
  have hr := Nat.mod_lt (modulus - 1) hn
  have heq : (modulus - 1) % n + n * q = modulus - 1 :=
    Nat.mod_add_div (modulus - 1) n
  have hna : n ≤ n * q := by nlinarith
  have hcredit := WordIntervals.remainder_expectation n q hq F
  have hk : smallKernel modulus n F ε =
      UniformRejection.kernel (n * q) (fun r => F (r % n)) ε := by
    funext r
    by_cases h : r < n
    · simp only [smallKernel, UniformRejection.kernel, ite_eq_left h,
        ite_eq_left (lt_of_lt_of_le h hna), Nat.mod_eq_of_lt h]
    · simp only [smallKernel, UniformRejection.kernel, ite_eq_right h, hcredit, limit, q]
      rfl
  rw [hk, UniformInt.lintegral_law]
  simpa only [hcredit] using UniformRejection.expectation (n * q) modulus
    (Nat.mul_pos hn hq) (by omega) (by omega) (fun r => F (r % n)) ε

def width (modulus n : ℕ) : ℕ := (n - 1) / modulus + 1

theorem width_pos (modulus n : ℕ) : 0 < width modulus n := by
  exact Nat.succ_pos _

instance (modulus n : ℕ) : NeZero (width modulus n) := ⟨(width_pos modulus n).ne'⟩

theorem width_lt (modulus n : ℕ) (hm : 2 ≤ modulus) (hmn : modulus < n) :
    width modulus n < n := by
  have h := Nat.div_lt_self (show 0 < n - 1 by omega) (show 1 < modulus by omega)
  unfold width
  omega

/-- The recursive rectangle covers the target and has less than twice its width. -/
theorem rectangle_bounds (modulus n : ℕ) (hm : 2 ≤ modulus) (hmn : modulus < n) :
    n ≤ width modulus n * modulus ∧ width modulus n * modulus ≤ 2 * n := by
  have hr := Nat.mod_lt (n - 1) (show 0 < modulus by omega)
  have heq := Nat.mod_add_div (n - 1) modulus
  have hdiv := Nat.div_mul_le_self (n - 1) modulus
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  unfold width
  constructor <;> nlinarith

/-- Independent high/low digits preserve the enclosing uniform rejection kernel. -/
theorem large_expectation (modulus n : ℕ) (hm : 2 ≤ modulus) (hmn : modulus < n)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ high, (∫⁻ low, UniformRejection.kernel n F ε (width modulus n * high + low)
      ∂UniformInt.law (width modulus n)) ∂UniformInt.law modulus ≤
        (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  rw [UniformRectangles.expectation, UniformInt.lintegral_law]
  exact UniformRejection.expectation n _ (by omega) (rectangle_bounds modulus n hm hmn).1
    (rectangle_bounds modulus n hm hmn).2 F ε

end

end SampLib.ModulusReduction
