import SampLib.Bernoulli.Laws.PiProbability
import SampLib.Bernoulli.Laws.ReciprocalPiProbability
import SampLib.Bernoulli.Support.RealEnclosureEncoding

/-! # Program values of the Machin enclosures

The π gateways return integer triples. This module identifies the encoded enclosures of π,
of its affine transforms, and of its reciprocal multiples with explicit triples.
-/

namespace SampLib.PiBounds

/-- The π enclosure encodes as its raw Machin triple. -/
@[simp] theorem encode_interval {rT : Type} (n : ℕ) :
    RealEnclosure.encodeInterval (rT := rT) (interval n) =
      RealEnclosure.encodeTriple (piRaw n) := by
  rw [RealEnclosure.encodeInterval, interval_triple]

end SampLib.PiBounds

namespace SampLib.PiProbability

/-- The affine π enclosure encodes as the shifted and scaled Machin triple. -/
theorem affine_encode {rT : Type} (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (affineInterval offset divisor hd hlo hhi n) =
      RealEnclosure.encodeTriple
        ((PiBounds.piRaw n).1 - offset * (PiBounds.piRaw n).2.2,
          ((PiBounds.piRaw n).2.1 - offset * (PiBounds.piRaw n).2.2,
            (divisor : ℤ) * (PiBounds.piRaw n).2.2)) := by
  simp [affineInterval, FromBounds.encodeInterval, RealEnclosure.encodeTriple,
    RealEnclosure.Interval.toProbability,
    RealEnclosure.Interval.affine, PiBounds.interval,
    Int.toNat_of_nonneg (PiBounds.piRaw_den_pos n).le]

end SampLib.PiProbability

namespace SampLib.ReciprocalPiProbability

/-- The reciprocal π enclosure encodes as the cross-multiplied Machin triple. -/
theorem encode {rT : Type} (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (interval numerator denominator hd hp n) =
      RealEnclosure.encodeTriple
        ((numerator : ℤ) * (PiBounds.piRaw n).2.2 * (PiBounds.piRaw n).1,
          ((numerator : ℤ) * (PiBounds.piRaw n).2.2 * (PiBounds.piRaw n).2.1,
            (denominator : ℤ) * (PiBounds.piRaw n).1 * (PiBounds.piRaw n).2.1)) := by
  change RealEnclosure.encodeInterval
    ((rational numerator denominator hd).quotient (PiBounds.interval n)
      (by positivity) (pi_left_pos n)) = _
  rw [RealEnclosure.encodeInterval, RealEnclosure.Interval.quotient_triple]
  simp only [rational, PiBounds.interval,
    Int.toNat_of_nonneg (PiBounds.piRaw_den_pos n).le]

end SampLib.ReciprocalPiProbability
