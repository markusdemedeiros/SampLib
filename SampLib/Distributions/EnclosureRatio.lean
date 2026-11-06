import SampLib.Distributions.RealEnclosure

/-! # Quotients with a positive denominator enclosure -/

namespace SampLib.RealEnclosure

noncomputable section

namespace Interval

variable {x y : ℝ} (a : Interval x) (b : Interval y)

private theorem lower_pos (hb : 0 < b.left) : 0 < b.lower := by
  have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
  have h : (0 : ℝ) < b.lower := (div_pos_iff_of_pos_right hd).mp hb
  exact_mod_cast h

private theorem upper_pos (hb : 0 < b.left) : 0 < b.upper := by
  have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
  have h : (0 : ℝ) < b.upper :=
    (div_pos_iff_of_pos_right hd).mp (hb.trans_le (b.left_le.trans b.le_right))
  exact_mod_cast h

private theorem lower_toNat (hb : 0 < b.left) : (b.lower.toNat : ℝ) = b.lower := by
  exact_mod_cast Int.toNat_of_nonneg (lower_pos b hb).le

private theorem upper_toNat (hb : 0 < b.left) : (b.upper.toNat : ℝ) = b.upper := by
  exact_mod_cast Int.toNat_of_nonneg (upper_pos b hb).le

/-- The integer arithmetic used by the `eOverPi` oracle. -/
def quotient (hx : 0 ≤ x) (hb : 0 < b.left) : Interval (x / y) where
  lower := a.lower * (b.denominator : ℤ) * b.lower
  upper := a.upper * (b.denominator : ℤ) * b.upper
  denominator := a.denominator * b.lower.toNat * b.upper.toNat
  positive := Nat.mul_pos (Nat.mul_pos a.positive
    (by have := lower_pos b hb; omega)) (by have := upper_pos b hb; omega)
  below := by
    have ha : (0 : ℝ) < a.denominator := by exact_mod_cast a.positive
    have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
    have hl : (0 : ℝ) < b.lower := by exact_mod_cast lower_pos b hb
    have hu : (0 : ℝ) < b.upper := by exact_mod_cast upper_pos b hb
    have hy : 0 < y := hb.trans_le b.left_le
    have h₁ : a.left / b.right ≤ x / y :=
      (div_le_div_of_nonneg_right a.left_le ((hb.trans_le (b.left_le.trans b.le_right)).le)).trans
        (div_le_div_of_nonneg_left hx hy b.le_right)
    push_cast
    rw [lower_toNat b hb, upper_toNat b hb]
    dsimp [left, right] at h₁
    field_simp at h₁ ⊢
    nlinarith
  above := by
    have ha : (0 : ℝ) < a.denominator := by exact_mod_cast a.positive
    have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
    have hl : (0 : ℝ) < b.lower := by exact_mod_cast lower_pos b hb
    have hu : (0 : ℝ) < b.upper := by exact_mod_cast upper_pos b hb
    have hy : 0 < y := hb.trans_le b.left_le
    have h₁ : x / y ≤ a.right / b.left :=
      (div_le_div_of_nonneg_left hx hb b.left_le).trans
        (div_le_div_of_nonneg_right a.le_right hb.le)
    push_cast
    rw [lower_toNat b hb, upper_toNat b hb]
    dsimp [left, right] at h₁
    field_simp at h₁ ⊢
    nlinarith

theorem quotient_left (hx : 0 ≤ x) (hb : 0 < b.left) :
    (a.quotient b hx hb).left = a.left / b.right := by
  have ha : (0 : ℝ) < a.denominator := by exact_mod_cast a.positive
  have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
  have hl : (0 : ℝ) < b.lower := by exact_mod_cast lower_pos b hb
  have hu : (0 : ℝ) < b.upper := by exact_mod_cast upper_pos b hb
  simp only [left, right, quotient, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    lower_toNat b hb, upper_toNat b hb]
  field_simp

theorem quotient_right (hx : 0 ≤ x) (hb : 0 < b.left) :
    (a.quotient b hx hb).right = a.right / b.left := by
  have ha : (0 : ℝ) < a.denominator := by exact_mod_cast a.positive
  have hd : (0 : ℝ) < b.denominator := by exact_mod_cast b.positive
  have hl : (0 : ℝ) < b.lower := by exact_mod_cast lower_pos b hb
  have hu : (0 : ℝ) < b.upper := by exact_mod_cast upper_pos b hb
  simp only [left, right, quotient, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    lower_toNat b hb, upper_toNat b hb]
  field_simp

theorem quotient_triple (hx : 0 ≤ x) (hb : 0 < b.left) :
    (a.quotient b hx hb).triple =
      (a.lower * (b.denominator : ℤ) * b.lower,
        (a.upper * (b.denominator : ℤ) * b.upper,
          (a.denominator : ℤ) * b.lower * b.upper)) := by
  simp only [triple, quotient, Nat.cast_mul,
    Int.toNat_of_nonneg (lower_pos b hb).le, Int.toNat_of_nonneg (upper_pos b hb).le]

end Interval

end

end SampLib.RealEnclosure
