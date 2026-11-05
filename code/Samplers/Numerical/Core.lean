import Samplers.Numeric

/-!
Fixed-point scalar conventions, uniform intervals, and exponential sampling.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

/-- Saturate a strictly positive numerical variate to the first positive grid cell.
This keeps subsequent logarithms/ratios defined when quantization would give zero. -/
@[pl_fold] def positiveGrid : Exp rT := pl%
  fun x, if x <= #0 then #1 else x

/-- Numerical uniform on [lo,hi); a narrow interval can quantize to its lower endpoint. -/
@[pl_fold] def uniformRange : Exp rT := pl%
  fun scale lo hi u,
    if hi <= lo then fail else
      lo + &Numeric.mul scale (hi - lo) (&Numeric.uniform scale #())

/-- Exponential with positive rate, by inverse transformation. -/
@[pl_fold] def exponential : Exp rT := pl%
  fun scale rate u,
    if rate <= #0 then fail else
      &positiveGrid (&Numeric.div scale (-(&Numeric.log scale (&Numeric.uniform scale #()))) rate)

end Occil.Numerical
