import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-! # Exact fractions for the factory engines

A fraction is an unreduced integer pair with a positive denominator. Its value is the
rational quotient, and the arithmetic lemmas state each source operation on values.
-/

namespace SampLib.FactoryFractions

/-- An unreduced source pair with a positive denominator. -/
structure Fraction where
  numerator : ℤ
  denominator : ℕ
  positive : 0 < denominator

def Fraction.value (a : Fraction) : ℚ := mkRat a.numerator a.denominator

/-- The result of source normalization. -/
def Fraction.ofRat (q : ℚ) : Fraction := ⟨q.num, q.den, q.den_pos⟩

@[simp] theorem Fraction.value_ofRat (q : ℚ) : (Fraction.ofRat q).value = q := by
  exact Rat.mkRat_self q

theorem add_value (a b : Fraction) :
    mkRat (a.numerator * b.denominator + b.numerator * a.denominator)
      (a.denominator * b.denominator) = a.value + b.value := by
  exact (Rat.mkRat_add_mkRat a.numerator b.numerator
    (Nat.ne_of_gt a.positive) (Nat.ne_of_gt b.positive)).symm

theorem subtract_value (a b : Fraction) :
    mkRat (a.numerator * b.denominator - b.numerator * a.denominator)
      (a.denominator * b.denominator) = a.value - b.value := by
  simp only [Fraction.value, sub_eq_add_neg, Rat.neg_mkRat]
  simpa only [neg_mul] using
    (Rat.mkRat_add_mkRat a.numerator (-b.numerator)
      (Nat.ne_of_gt a.positive) (Nat.ne_of_gt b.positive)).symm

/-- The encoded rational pair has its literal quotient as mathematical value. -/
theorem Fraction.cast_value (a : Fraction) :
    (a.value : ℝ) = (a.numerator : ℝ) / (a.denominator : ℝ) :=
  Rat.cast_mkRat_of_ne_zero a.numerator (by exact_mod_cast (Nat.ne_of_gt a.positive))

theorem multiply_value (a b : Fraction) :
    mkRat (a.numerator * b.numerator) (a.denominator * b.denominator) = a.value * b.value :=
  (Rat.mkRat_mul_mkRat a.numerator b.numerator a.denominator b.denominator).symm

theorem divide_value (a b : Fraction) (hb : 0 < b.numerator) :
    mkRat (a.numerator * b.denominator) (a.denominator * b.numerator.toNat) =
      a.value / b.value := by
  have ha : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt a.positive)
  have hd : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.positive)
  have hn : (b.numerator : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (b.numerator.toNat : ℚ) = b.numerator := by
    exact_mod_cast Int.toNat_of_nonneg hb.le
  simp only [Fraction.value, Rat.mkRat_eq_div, Nat.cast_mul, Int.cast_mul,
    Int.cast_natCast, hc]
  field_simp

end SampLib.FactoryFractions
