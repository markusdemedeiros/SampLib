import SampLib.Bernoulli.Laws.EulerEnclosure
import SampLib.Bernoulli.Laws.EnclosureRatioLimits

/-! # The shifted reciprocal enclosures used by `inverseEPlusRational` -/

namespace SampLib.EulerReciprocal

noncomputable section

def center (a b : ℕ) : ℝ := Real.exp 1 + (a : ℝ) / b - 2

theorem center_ge_one (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) : 1 ≤ center a b := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : (1 : ℝ) ≤ (a : ℝ) / b := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (show (b : ℝ) ≤ a by exact_mod_cast hab)
  dsimp [center]
  linarith

def low (a b n : ℕ) : ℤ :=
  (EulerEnclosure.interval n).lower * b + ((a : ℤ) - 2 * b) *
    (EulerEnclosure.interval n).denominator

def high (a b n : ℕ) : ℤ :=
  (EulerEnclosure.interval n).upper * b + ((a : ℤ) - 2 * b) *
    (EulerEnclosure.interval n).denominator

theorem low_ge_denominator (a b n : ℕ) (hab : b ≤ a) :
    (b : ℤ) * (EulerEnclosure.interval n).denominator ≤ low a b n := by
  have h := mul_le_mul_of_nonneg_right (EulerEnclosure.lower_ge_two n)
    (show (0 : ℤ) ≤ b by positivity)
  have h' := mul_le_mul_of_nonneg_right (show (b : ℤ) ≤ a by exact_mod_cast hab)
    (show (0 : ℤ) ≤ (EulerEnclosure.interval n).denominator by positivity)
  dsimp [low]
  nlinarith

theorem low_pos (a b n : ℕ) (hb : 0 < b) (hab : b ≤ a) : 0 < low a b n :=
  lt_of_lt_of_le (mul_pos (by exact_mod_cast hb)
    (by exact_mod_cast (EulerEnclosure.interval n).positive))
    (low_ge_denominator a b n hab)

/-- Shift the factorial enclosure by the exact rational `a/b - 2`. -/
def shifted (a b : ℕ) (hb : 0 < b) (n : ℕ) : RealEnclosure.Interval (center a b) where
  lower := low a b n
  upper := high a b n
  denominator := b * (EulerEnclosure.interval n).denominator
  positive := Nat.mul_pos hb (EulerEnclosure.interval n).positive
  below := by
    have h := mul_le_mul_of_nonneg_right (EulerEnclosure.interval n).below
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
    have hb' : (b : ℝ) ≠ 0 := by positivity
    dsimp [low, center]
    push_cast
    field_simp
    nlinarith
  above := by
    have h := mul_le_mul_of_nonneg_right (EulerEnclosure.interval n).above
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
    have hb' : (b : ℝ) ≠ 0 := by positivity
    dsimp [high, center]
    push_cast
    field_simp
    nlinarith

theorem shifted_width (a b : ℕ) (hb : 0 < b) (n : ℕ) :
    (shifted a b hb n).width = (EulerEnclosure.interval n).width := by
  simp only [RealEnclosure.Interval.width, RealEnclosure.Interval.left,
    RealEnclosure.Interval.right, shifted, low, high]
  push_cast
  have hb' : (b : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem shifted_left_pos (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    0 < (shifted a b hb n).left := by
  apply div_pos
  · exact_mod_cast low_pos a b n hb hab
  · exact_mod_cast (shifted a b hb n).positive

private def one : RealEnclosure.Interval (1 : ℝ) where
  lower := 1
  upper := 1
  denominator := 1
  positive := by decide
  below := by norm_num
  above := by norm_num

/-- Take the reciprocal, retaining the source's unreduced common denominator. -/
def interval (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    RealEnclosure.Interval (1 / center a b) :=
  one.quotient (shifted a b hb n) (by norm_num) (shifted_left_pos a b hb hab n)

theorem triple_eq (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    (interval a b hb hab n).triple =
      ((b : ℤ) * (EulerEnclosure.interval n).denominator * low a b n,
        ((b : ℤ) * (EulerEnclosure.interval n).denominator * high a b n,
          low a b n * high a b n)) := by
  rw [interval, RealEnclosure.Interval.quotient_triple]
  simp [one, shifted, Nat.cast_mul]

theorem denominator_cast (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    ((interval a b hb hab n).denominator : ℤ) = low a b n * high a b n :=
  congrArg (fun t : ℤ × (ℤ × ℤ) => t.2.2) (triple_eq a b hb hab n)

theorem width_tendsto (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    Filter.Tendsto (fun n => (interval a b hb hab n).width) Filter.atTop (nhds 0) := by
  apply RealEnclosure.quotient_width_tendsto (fun _ => one) (shifted a b hb)
    (by norm_num) (shifted_left_pos a b hb hab)
  · simpa only [RealEnclosure.Interval.width, RealEnclosure.Interval.left,
      RealEnclosure.Interval.right, one, sub_self] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  · simpa only [shifted_width] using EulerEnclosure.width_tendsto

theorem tight (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    RealEnclosure.Tight (interval a b hb hab) :=
  RealEnclosure.Tight.of_tendsto _ (width_tendsto a b hb hab)

end

end SampLib.EulerReciprocal
