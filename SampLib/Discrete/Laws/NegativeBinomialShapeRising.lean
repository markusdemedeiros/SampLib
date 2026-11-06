import SampLib.Discrete.Laws.MultichooseSeries
import SampLib.Discrete.Laws.PolyaEggenberger

/-! # The source's integer rising products equal real multichoose ratios -/

open scoped ENNReal

namespace SampLib.NegativeBinomialShape

noncomputable section

open PolyaEggenberger (rising)

theorem rising_succ_right (A B n : ℕ) :
    rising A B (n + 1) = rising A B n * (A + n * B) := by
  induction n generalizing A with
  | zero => simp [rising]
  | succ n ih =>
    change A * rising (A + B) B (n + 1) =
      (A * rising (A + B) B n) * (A + (n + 1) * B)
    rw [ih]
    ring

theorem rising_pos {A : ℕ} (hA : 0 < A) (B n : ℕ) : 0 < rising A B n := by
  induction n generalizing A with
  | zero => simp [rising]
  | succ n ih =>
    rw [rising]
    exact Nat.mul_pos hA (ih (by omega))

theorem rising_mono {A C : ℕ} (hAC : A ≤ C) (B n : ℕ) : rising A B n ≤ rising C B n := by
  induction n generalizing A C with
  | zero => simp [rising]
  | succ n ih =>
    rw [rising, rising]
    exact Nat.mul_le_mul hAC (ih (by omega))

/-- Scaling the ascending product by its step leaves a factorial times multichoose. -/
theorem rising_eq_multichoose (A B n : ℕ) (hB : 0 < B) :
    (rising A B n : ℝ) =
      (B : ℝ) ^ n * (n.factorial : ℝ) * Ring.multichoose ((A : ℝ) / B) n := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    rw [rising_succ_right, Nat.cast_mul, ih, MultichooseSeries.step]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

/-- The callback's exact integer quotient is the generalized coefficient quotient. -/
theorem rising_ratio_eq (A B M n : ℕ) (hB : 0 < B) (hM : 0 < M) :
    (rising A B n : ℝ) / rising (M * B) B n =
      Ring.multichoose ((A : ℝ) / B) n / Ring.multichoose (M : ℝ) n := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hshape : ((M * B : ℕ) : ℝ) / B = (M : ℝ) := by
    rw [Nat.cast_mul, mul_div_cancel_right₀ _ hB0]
  rw [rising_eq_multichoose A B n hB, rising_eq_multichoose (M * B) B n hB, hshape]
  have hcommon : (B : ℝ) ^ n * (n.factorial : ℝ) ≠ 0 := by positivity
  have hcoef : Ring.multichoose (M : ℝ) n ≠ 0 :=
    (MultichooseSeries.pos (by exact_mod_cast hM) n).ne'
  field_simp

/-- The integer acceptance ratio stays in the coin domain whenever the shape is bounded by `M`. -/
theorem rising_ratio_mem (A B M n : ℕ) (hB : 0 < B) (hM : 0 < M) (hAM : A ≤ M * B) :
    (rising A B n : ℝ) / rising (M * B) B n ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < rising (M * B) B n := by
    exact_mod_cast rising_pos (Nat.mul_pos hM hB) B n
  exact ⟨div_nonneg (by positivity) hd.le,
    (div_le_one hd).mpr (by exact_mod_cast rising_mono hAM B n)⟩

end

end SampLib.NegativeBinomialShape
