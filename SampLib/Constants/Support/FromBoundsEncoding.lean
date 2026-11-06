import SampLib.Common.Laws.BoundsKernel
import Metrology.ProbLang.Syntax.Syntax

/-! # Program encoding of rational enclosures

The `fromBounds` engine reads each enclosure as the nested tuple
`(lower, (upper, denominator))`.
-/

open ProbLang

namespace SampLib.FromBounds

/-- The source callback representation `(lower,(upper,denominator))`. -/
def encodeInterval {rT : Type} {p : unitInterval} (a : Interval p) : Val rT :=
  Val.pair (Val.int a.lower) (Val.pair (Val.int a.upper) (Val.int a.denominator))

end SampLib.FromBounds
