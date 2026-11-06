module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Rational enclosures for shared latent reals

All statements are pointwise. In particular, multiplication may use two intervals
for the same latent value; no independence assumption enters interval arithmetic.
-/

namespace SampLib.LatentReal

/-- A closed rational interval with a common positive denominator. -/
structure RationalInterval where
  lower : ℤ
  upper : ℤ
  denominator : ℤ
  denominator_pos : 0 < denominator
  lower_le_upper : lower ≤ upper

namespace RationalInterval

noncomputable section

variable (a b : RationalInterval)

/-- Lower endpoint, interpreted in mathematical reals. -/
def lowerReal : ℝ := a.lower / a.denominator

/-- Upper endpoint, interpreted in mathematical reals. -/
def upperReal : ℝ := a.upper / a.denominator

/-- An interval encloses a latent value. -/
def Contains (x : ℝ) : Prop := a.lowerReal ≤ x ∧ x ≤ a.upperReal

theorem denominatorReal_pos : (0 : ℝ) < a.denominator := by
  exact_mod_cast a.denominator_pos

theorem lowerReal_le_upperReal : a.lowerReal ≤ a.upperReal :=
  div_le_div_of_nonneg_right (by exact_mod_cast a.lower_le_upper)
    a.denominatorReal_pos.le

/-- A rational constant is already a zero-width enclosure. -/
def point (numerator denominator : ℤ) (hd : 0 < denominator) : RationalInterval where
  lower := numerator
  upper := numerator
  denominator := denominator
  denominator_pos := hd
  lower_le_upper := le_rfl

@[simp] theorem contains_point (numerator denominator : ℤ) (hd : 0 < denominator) (x : ℝ) :
    (point numerator denominator hd).Contains x ↔ x = numerator / denominator :=
  le_antisymm_iff.symm.trans eq_comm

/-- Negation reverses the two endpoints. -/
def negate : RationalInterval where
  lower := -a.upper
  upper := -a.lower
  denominator := a.denominator
  denominator_pos := a.denominator_pos
  lower_le_upper := neg_le_neg a.lower_le_upper

@[simp] theorem lowerReal_negate : a.negate.lowerReal = -a.upperReal := by
  simp [negate, lowerReal, upperReal, neg_div]

@[simp] theorem upperReal_negate : a.negate.upperReal = -a.lowerReal := by
  simp [negate, lowerReal, upperReal, neg_div]

theorem contains_negate {x : ℝ} (hx : a.Contains x) : a.negate.Contains (-x) := by
  simpa only [Contains, lowerReal_negate, upperReal_negate, neg_le_neg_iff] using
    And.intro hx.2 hx.1

/-- Addition uses the product denominator, exactly as the interval oracle does. -/
def add : RationalInterval where
  lower := a.lower * b.denominator + b.lower * a.denominator
  upper := a.upper * b.denominator + b.upper * a.denominator
  denominator := a.denominator * b.denominator
  denominator_pos := mul_pos a.denominator_pos b.denominator_pos
  lower_le_upper := add_le_add
    (mul_le_mul_of_nonneg_right a.lower_le_upper b.denominator_pos.le)
    (mul_le_mul_of_nonneg_right b.lower_le_upper a.denominator_pos.le)

@[simp] theorem lowerReal_add : (a.add b).lowerReal = a.lowerReal + b.lowerReal := by
  dsimp [add, lowerReal]
  push_cast
  simpa only [mul_comm] using
    (div_add_div _ _ (ne_of_gt a.denominatorReal_pos) (ne_of_gt b.denominatorReal_pos)).symm

@[simp] theorem upperReal_add : (a.add b).upperReal = a.upperReal + b.upperReal := by
  dsimp [add, upperReal]
  push_cast
  simpa only [mul_comm] using
    (div_add_div _ _ (ne_of_gt a.denominatorReal_pos) (ne_of_gt b.denominatorReal_pos)).symm

theorem contains_add {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  simpa only [Contains, lowerReal_add, upperReal_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

/-- Rational scaling reverses bounds exactly when its numerator is negative. -/
def scaleRational (numerator denominator : ℤ) (hd : 0 < denominator) : RationalInterval where
  lower := if numerator < 0 then a.upper * numerator else a.lower * numerator
  upper := if numerator < 0 then a.lower * numerator else a.upper * numerator
  denominator := a.denominator * denominator
  denominator_pos := mul_pos a.denominator_pos hd
  lower_le_upper := by
    split_ifs with hn
    · exact mul_le_mul_of_nonpos_right a.lower_le_upper hn.le
    · exact mul_le_mul_of_nonneg_right a.lower_le_upper (le_of_not_gt hn)

@[simp] theorem lowerReal_scaleRational (numerator denominator : ℤ) (hd : 0 < denominator) :
    (a.scaleRational numerator denominator hd).lowerReal =
      (if numerator < 0 then a.upperReal else a.lowerReal) * (numerator / denominator) := by
  by_cases hn : numerator < 0 <;>
    simp [scaleRational, lowerReal, upperReal, hn, div_mul_div_comm]

@[simp] theorem upperReal_scaleRational (numerator denominator : ℤ) (hd : 0 < denominator) :
    (a.scaleRational numerator denominator hd).upperReal =
      (if numerator < 0 then a.lowerReal else a.upperReal) * (numerator / denominator) := by
  by_cases hn : numerator < 0 <;>
    simp [scaleRational, lowerReal, upperReal, hn, div_mul_div_comm]

theorem contains_scaleRational (numerator denominator : ℤ) (hd : 0 < denominator)
    {x : ℝ} (hx : a.Contains x) :
    (a.scaleRational numerator denominator hd).Contains (x * (numerator / denominator)) := by
  have hden : (0 : ℝ) < denominator := by exact_mod_cast hd
  by_cases hn : numerator < 0
  · have hq : (numerator : ℝ) / denominator ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn.le) hden.le
    simpa only [Contains, lowerReal_scaleRational, upperReal_scaleRational, ite_eq_left hn] using
      And.intro (mul_le_mul_of_nonpos_right hx.2 hq) (mul_le_mul_of_nonpos_right hx.1 hq)
  · have hq : (0 : ℝ) ≤ numerator / denominator :=
      div_nonneg (by exact_mod_cast le_of_not_gt hn) hden.le
    simpa only [Contains, lowerReal_scaleRational, upperReal_scaleRational, ite_eq_right hn] using
      And.intro (mul_le_mul_of_nonneg_right hx.1 hq) (mul_le_mul_of_nonneg_right hx.2 hq)

private theorem mul_bounds {lo hi x : ℝ} (hx : lo ≤ x ∧ x ≤ hi) (y : ℝ) :
    min (lo * y) (hi * y) ≤ x * y ∧ x * y ≤ max (lo * y) (hi * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

private theorem mul_rectangle_bounds {al ah bl bh x y : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh)) ≤ x * y ∧
      x * y ≤ max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)) := by
  have ha := mul_bounds hy al
  have hb := mul_bounds hy ah
  simp only [mul_comm bl, mul_comm bh, mul_comm y] at ha hb
  exact ⟨(min_le_min ha.1 hb.1).trans (mul_bounds hx y).1,
    (mul_bounds hx y).2.trans (max_le_max ha.2 hb.2)⟩

/-- Four-corner multiplication, valid also for aliases of one interval oracle. -/
def multiply : RationalInterval where
  lower := min (min (a.lower * b.lower) (a.lower * b.upper))
    (min (a.upper * b.lower) (a.upper * b.upper))
  upper := max (max (a.lower * b.lower) (a.lower * b.upper))
    (max (a.upper * b.lower) (a.upper * b.upper))
  denominator := a.denominator * b.denominator
  denominator_pos := mul_pos a.denominator_pos b.denominator_pos
  lower_le_upper :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans
      ((le_max_left _ _).trans (le_max_left _ _))

@[simp] theorem lowerReal_multiply :
    (a.multiply b).lowerReal =
      min (min (a.lowerReal * b.lowerReal) (a.lowerReal * b.upperReal))
        (min (a.upperReal * b.lowerReal) (a.upperReal * b.upperReal)) := by
  have hd : (0 : ℝ) ≤ a.denominator * b.denominator :=
    (mul_pos a.denominatorReal_pos b.denominatorReal_pos).le
  simp only [multiply, lowerReal, upperReal, Int.cast_min, Int.cast_mul,
    div_mul_div_comm, min_div_div_right hd]

@[simp] theorem upperReal_multiply :
    (a.multiply b).upperReal =
      max (max (a.lowerReal * b.lowerReal) (a.lowerReal * b.upperReal))
        (max (a.upperReal * b.lowerReal) (a.upperReal * b.upperReal)) := by
  have hd : (0 : ℝ) ≤ a.denominator * b.denominator :=
    (mul_pos a.denominatorReal_pos b.denominatorReal_pos).le
  simp only [multiply, lowerReal, upperReal, Int.cast_max, Int.cast_mul,
    div_mul_div_comm, max_div_div_right hd]

theorem contains_multiply {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.multiply b).Contains (x * y) := by
  simpa only [Contains, lowerReal_multiply, upperReal_multiply] using
    mul_rectangle_bounds hx hy

/-- A reciprocal is available once refinement has separated the interval from zero. -/
def reciprocal (hzero : 0 < a.lower ∨ a.upper < 0) : RationalInterval where
  lower := a.denominator * a.lower
  upper := a.denominator * a.upper
  denominator := a.lower * a.upper
  denominator_pos := by
    rcases hzero with h | h
    · exact mul_pos h (h.trans_le a.lower_le_upper)
    · exact mul_pos_of_neg_of_neg (a.lower_le_upper.trans_lt h) h
  lower_le_upper := mul_le_mul_of_nonneg_left a.lower_le_upper a.denominator_pos.le

private theorem endpoints_ne_zero (hzero : 0 < a.lower ∨ a.upper < 0) :
    a.lower ≠ 0 ∧ a.upper ≠ 0 := by
  rcases hzero with h | h
  · exact ⟨ne_of_gt h, ne_of_gt (h.trans_le a.lower_le_upper)⟩
  · exact ⟨ne_of_lt (a.lower_le_upper.trans_lt h), ne_of_lt h⟩

@[simp] theorem lowerReal_reciprocal (hzero : 0 < a.lower ∨ a.upper < 0) :
    (a.reciprocal hzero).lowerReal = 1 / a.upperReal := by
  dsimp [reciprocal, lowerReal, upperReal]
  push_cast
  have hl : (a.lower : ℝ) ≠ 0 := by exact_mod_cast (a.endpoints_ne_zero hzero).1
  have hu : (a.upper : ℝ) ≠ 0 := by exact_mod_cast (a.endpoints_ne_zero hzero).2
  field_simp

@[simp] theorem upperReal_reciprocal (hzero : 0 < a.lower ∨ a.upper < 0) :
    (a.reciprocal hzero).upperReal = 1 / a.lowerReal := by
  dsimp [reciprocal, lowerReal, upperReal]
  push_cast
  have hl : (a.lower : ℝ) ≠ 0 := by exact_mod_cast (a.endpoints_ne_zero hzero).1
  have hu : (a.upper : ℝ) ≠ 0 := by exact_mod_cast (a.endpoints_ne_zero hzero).2
  field_simp

theorem contains_reciprocal (hzero : 0 < a.lower ∨ a.upper < 0)
    {x : ℝ} (hx : a.Contains x) : (a.reciprocal hzero).Contains (1 / x) := by
  simp only [Contains, lowerReal_reciprocal, upperReal_reciprocal]
  rcases hzero with h | h
  · have hl : 0 < a.lowerReal := div_pos (by exact_mod_cast h) a.denominatorReal_pos
    exact ⟨one_div_le_one_div_of_le (hl.trans_le hx.1) hx.2,
      one_div_le_one_div_of_le hl hx.1⟩
  · have hu : a.upperReal < 0 := div_neg_of_neg_of_pos
      (by exact_mod_cast h) a.denominatorReal_pos
    exact ⟨one_div_le_one_div_of_neg_of_le hu hx.2,
      one_div_le_one_div_of_neg_of_le (hx.2.trans_lt hu) hx.1⟩

/-- Width tracks the precision independently of the particular oracle schedule. -/
def width : ℝ := a.upperReal - a.lowerReal

theorem width_nonneg : 0 ≤ a.width := sub_nonneg.mpr a.lowerReal_le_upperReal

@[simp] theorem width_negate : a.negate.width = a.width := by
  simp [width, sub_eq_add_neg, add_comm]

@[simp] theorem width_add : (a.add b).width = a.width + b.width := by
  simp only [width, lowerReal_add, upperReal_add]
  ring

end

end RationalInterval

end SampLib.LatentReal
