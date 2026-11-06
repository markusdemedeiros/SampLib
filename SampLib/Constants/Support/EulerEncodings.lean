import SampLib.Constants.Laws.EulerConstants
import SampLib.Constants.Laws.EulerHyperbolic
import SampLib.Bernoulli.Support.RealEnclosureEncoding

/-! # Program encodings of the factorial-enclosure constants

Each lemma rewrites a derived enclosure's callback value into the integer triple that the
source program computes from the factorial enclosure of `e`.
-/

namespace SampLib.EulerConstants

theorem minusTwo_encode {rT : Type} (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (minusTwoInterval n) =
      RealEnclosure.encodeTriple
        ((EulerEnclosure.interval n).lower - 2 * (EulerEnclosure.interval n).denominator,
          ((EulerEnclosure.interval n).upper - 2 * (EulerEnclosure.interval n).denominator,
            (EulerEnclosure.interval n).denominator)) := by
  simp [minusTwoInterval, FromBounds.encodeInterval, RealEnclosure.Interval.affine,
    RealEnclosure.Interval.toProbability, RealEnclosure.encodeTriple]

theorem threeMinus_encode {rT : Type} (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (threeMinusInterval n) =
      RealEnclosure.encodeTriple
        (3 * (EulerEnclosure.interval n).denominator - (EulerEnclosure.interval n).upper,
          (3 * (EulerEnclosure.interval n).denominator - (EulerEnclosure.interval n).lower,
            (EulerEnclosure.interval n).denominator)) := rfl

end SampLib.EulerConstants

namespace SampLib.EulerHyperbolic

theorem encode {rT : Type} (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (interval n) =
      RealEnclosure.encodeTriple
        (((EulerEnclosure.interval n).lower - (EulerEnclosure.interval n).denominator) *
            ((EulerEnclosure.interval n).upper + (EulerEnclosure.interval n).denominator),
          (((EulerEnclosure.interval n).upper - (EulerEnclosure.interval n).denominator) *
            ((EulerEnclosure.interval n).lower + (EulerEnclosure.interval n).denominator),
            ((EulerEnclosure.interval n).lower + (EulerEnclosure.interval n).denominator) *
              ((EulerEnclosure.interval n).upper + (EulerEnclosure.interval n).denominator))) := by
  have hl : ((lower n).toNat : ℤ) = lower n := Int.toNat_of_nonneg (lower_pos n).le
  have hu : ((upper n).toNat : ℤ) = upper n := Int.toNat_of_nonneg (upper_pos n).le
  simp only [FromBounds.encodeInterval, interval, RealEnclosure.encodeTriple,
    Nat.cast_mul, hl, hu]
  rfl

end SampLib.EulerHyperbolic
