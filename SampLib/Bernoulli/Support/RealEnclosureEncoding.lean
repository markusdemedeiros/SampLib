import SampLib.Bernoulli.Laws.RealEnclosure
import SampLib.Constants.Support.FromBoundsEncoding

/-! # Program values of rational enclosures

Concrete enclosure gateways return the integer triple `(lower, (upper, denominator))` as a
program value. This module defines that encoding and relates it to `FromBounds`.
-/

namespace SampLib.RealEnclosure

/-- Encode an integer triple as nested program pairs. -/
def encodeTriple {rT : Type} (a : ℤ × (ℤ × ℤ)) : ProbLang.Val rT :=
  .pair (.int a.1) (.pair (.int a.2.1) (.int a.2.2))

/-- Encode an enclosure by its integer triple. -/
def encodeInterval {rT : Type} {x : ℝ} (a : Interval x) : ProbLang.Val rT :=
  encodeTriple a.triple

@[simp] theorem encode_toProbability {rT : Type} {x : ℝ} (a : Interval x)
    (p : unitInterval) (hx : (p : ℝ) = x) :
    FromBounds.encodeInterval (rT := rT) (a.toProbability p hx) = encodeInterval a := rfl

end SampLib.RealEnclosure
