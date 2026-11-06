import SampLib.Bernoulli.Laws.EulerNumberBounds
import SampLib.Bernoulli.Laws.RealEnclosure
import SampLib.Bernoulli.Laws.RealEnclosureTransforms

/-! # The monotone fractional-linear image of the factorial enclosure -/

open Filter
open scoped Topology

namespace SampLib.EulerHyperbolic

noncomputable section

abbrev bias : unitInterval :=
  ⟨(Real.exp 1 - 1) / (Real.exp 1 + 1),
    div_nonneg (by linarith [EulerNumber.exp_one_gt_two]) (by positivity),
    (div_le_one (by positivity)).mpr (by linarith)⟩

/-- The fractional-linear Euler expression is `tanh(1/2)`. -/
theorem bias_coe : (bias : ℝ) = Real.tanh (1 / 2) := by
  have he : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  change (Real.exp 1 - 1) / (Real.exp 1 + 1) = _
  rw [Real.tanh_eq, Real.exp_neg, he]
  field_simp

/-- The scaled lower endpoint of `e + 1`. -/
def lower (n : ℕ) : ℤ :=
  (EulerEnclosure.interval n).lower + (EulerEnclosure.interval n).denominator

/-- The scaled upper endpoint of `e + 1`. -/
def upper (n : ℕ) : ℤ :=
  (EulerEnclosure.interval n).upper + (EulerEnclosure.interval n).denominator

theorem lower_pos (n : ℕ) : 0 < lower n := by
  have hd : (0 : ℤ) < (EulerEnclosure.interval n).denominator := by
    exact_mod_cast (EulerEnclosure.interval n).positive
  have := EulerEnclosure.lower_ge_two n
  dsimp [lower]
  omega

theorem upper_pos (n : ℕ) : 0 < upper n := by
  have hd : (0 : ℝ) < (EulerEnclosure.interval n).denominator := by
    exact_mod_cast (EulerEnclosure.interval n).positive
  have he := Real.exp_pos (1 : ℝ)
  have ha := (EulerEnclosure.interval n).above
  have h : (0 : ℝ) < (upper n : ℝ) := by
    simp only [upper, Int.cast_add, Int.cast_natCast]
    nlinarith
  exact_mod_cast h

private theorem lower_toNat (n : ℕ) : ((lower n).toNat : ℝ) = lower n := by
  exact_mod_cast Int.toNat_of_nonneg (lower_pos n).le

private theorem upper_toNat (n : ℕ) : ((upper n).toNat : ℝ) = upper n := by
  exact_mod_cast Int.toNat_of_nonneg (upper_pos n).le

/-- `(x-1)/(x+1)` increases on the positive half-line. -/
private theorem monotone_ratio {a b : ℝ} (ha : 0 < a + 1) (hb : 0 < b + 1)
    (hab : a ≤ b) : (a - 1) / (a + 1) ≤ (b - 1) / (b + 1) := by
  apply (div_le_div_iff₀ ha hb).mpr
  nlinarith

private theorem lower_bound (n : ℕ) :
    ((EulerEnclosure.interval n).lower - (EulerEnclosure.interval n).denominator : ℝ) /
        lower n ≤ (bias : ℝ) := by
  have hd : (0 : ℝ) < (EulerEnclosure.interval n).denominator := by
    exact_mod_cast (EulerEnclosure.interval n).positive
  have hl : 0 < (EulerEnclosure.interval n).left + 1 := by
    rw [RealEnclosure.Interval.left, div_add_one (ne_of_gt hd)]
    exact div_pos (by exact_mod_cast lower_pos n) hd
  have h := monotone_ratio hl (by positivity) (EulerEnclosure.interval n).left_le
  convert h using 1
  simp only [RealEnclosure.Interval.left, lower,
      Int.cast_add, Int.cast_natCast]
  field_simp

private theorem upper_bound (n : ℕ) :
    (bias : ℝ) ≤
      ((EulerEnclosure.interval n).upper - (EulerEnclosure.interval n).denominator : ℝ) /
        upper n := by
  have hd : (0 : ℝ) < (EulerEnclosure.interval n).denominator := by
    exact_mod_cast (EulerEnclosure.interval n).positive
  have hu : 0 < (EulerEnclosure.interval n).right + 1 := by
    rw [RealEnclosure.Interval.right, div_add_one (ne_of_gt hd)]
    exact div_pos (by exact_mod_cast upper_pos n) hd
  have h := monotone_ratio (by positivity) hu (EulerEnclosure.interval n).le_right
  convert h using 1
  simp only [RealEnclosure.Interval.right, upper,
      Int.cast_add, Int.cast_natCast]
  field_simp

/-- The source keeps the two endpoint denominators as one positive integer product. -/
def interval (n : ℕ) : FromBounds.Interval bias where
  lower := ((EulerEnclosure.interval n).lower - (EulerEnclosure.interval n).denominator) *
    upper n
  upper := ((EulerEnclosure.interval n).upper - (EulerEnclosure.interval n).denominator) *
    lower n
  denominator := (lower n).toNat * (upper n).toNat
  positive := Nat.mul_pos (by have := lower_pos n; omega) (by have := upper_pos n; omega)
  below := by
    have hl : (0 : ℝ) < lower n := by exact_mod_cast lower_pos n
    have hu : (0 : ℝ) < upper n := by exact_mod_cast upper_pos n
    have h := (div_le_iff₀ hl).mp (lower_bound n)
    push_cast
    rw [lower_toNat, upper_toNat]
    nlinarith [mul_le_mul_of_nonneg_right h hu.le]
  above := by
    have hl : (0 : ℝ) < lower n := by exact_mod_cast lower_pos n
    have hu : (0 : ℝ) < upper n := by exact_mod_cast upper_pos n
    have h := (le_div_iff₀ hu).mp (upper_bound n)
    push_cast
    rw [lower_toNat, upper_toNat]
    nlinarith [mul_le_mul_of_nonneg_right h hl.le]

private theorem left_eq (n : ℕ) :
    (interval n).left = ((EulerEnclosure.interval n).left - 1) /
      ((EulerEnclosure.interval n).left + 1) := by
  have hd : ((EulerEnclosure.interval n).denominator : ℝ) ≠ 0 := by
    exact_mod_cast (EulerEnclosure.interval n).positive.ne'
  have hl : (lower n : ℝ) ≠ 0 := by exact_mod_cast (lower_pos n).ne'
  have hu : (upper n : ℝ) ≠ 0 := by exact_mod_cast (upper_pos n).ne'
  dsimp [FromBounds.Interval.left, interval, RealEnclosure.Interval.left]
  push_cast
  rw [lower_toNat, upper_toNat]
  dsimp [lower, upper] at hl hu ⊢
  push_cast at hl hu ⊢
  field_simp

private theorem right_eq (n : ℕ) :
    (interval n).right = ((EulerEnclosure.interval n).right - 1) /
      ((EulerEnclosure.interval n).right + 1) := by
  have hd : ((EulerEnclosure.interval n).denominator : ℝ) ≠ 0 := by
    exact_mod_cast (EulerEnclosure.interval n).positive.ne'
  have hl : (lower n : ℝ) ≠ 0 := by exact_mod_cast (lower_pos n).ne'
  have hu : (upper n : ℝ) ≠ 0 := by exact_mod_cast (upper_pos n).ne'
  dsimp [FromBounds.Interval.right, interval, RealEnclosure.Interval.right]
  push_cast
  rw [lower_toNat, upper_toNat]
  dsimp [lower, upper] at hl hu ⊢
  push_cast at hl hu ⊢
  field_simp

/-- Both transformed endpoints converge to the same fractional-linear image. -/
theorem width_tendsto : Tendsto (fun n => (interval n).width) atTop (nhds 0) := by
  have hl := RealEnclosure.left_tendsto EulerEnclosure.interval EulerEnclosure.width_tendsto
  have hu := RealEnclosure.right_tendsto EulerEnclosure.interval EulerEnclosure.width_tendsto
  have he : Real.exp 1 + 1 ≠ 0 := ne_of_gt (by positivity)
  simpa only [FromBounds.Interval.width, left_eq, right_eq, Pi.div_apply, sub_self] using
    ((hu.sub_const 1).div (hu.add_const 1) he).sub
      ((hl.sub_const 1).div (hl.add_const 1) he)

theorem tight : FromBounds.Tight interval := by
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp width_tendsto).2 ε hε).exists
  exact ⟨n, hn.le⟩

end

end SampLib.EulerHyperbolic
