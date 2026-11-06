import SampLib.Weighted.Laws.LemireUniform

/-! # Lazy thresholds for O'Neill's multiply-high reduction

The threshold computed by at most two subtractions equals the Euclidean remainder, and a low
word of at least `n` is always accepted.
-/

open scoped ENNReal

namespace SampLib.OneillUniform

noncomputable section

/-- The rejection threshold, computed with at most two subtractions before a remainder. -/
def threshold (n width : ℕ) : ℕ :=
  if width - n < n then width - n
  else if width - n - n < n then width - n - n else (width - n - n) % n

theorem threshold_eq (n width : ℕ) (hnw : n ≤ width) :
    threshold n width = width % n := by
  rw [Nat.mod_eq_sub_mod hnw]
  unfold threshold
  split_ifs with h₁ h₂
  · exact (Nat.mod_eq_of_lt h₁).symm
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h₁), Nat.mod_eq_of_lt h₂]
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h₁)]

theorem initial_expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ r, LemireUniform.kernel n width F 0 r ∂UniformInt.law width ≤
      ∫⁻ y, F y ∂UniformInt.law n := by
  simpa only [mul_zero, add_zero] using LemireUniform.expectation n width hn hnw F 0

theorem safe_low (n width low : ℕ) (hn : 0 < n) (h : n ≤ low) :
    ¬low < width % n := by
  have := Nat.mod_lt width hn
  omega

end

end SampLib.OneillUniform
