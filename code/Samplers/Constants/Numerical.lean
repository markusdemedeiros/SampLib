import Samplers.Numeric

/-!
# Numerical known-probability coins

These routines approximate the named probabilities on an explicit integer
Q(scale) grid. They are useful at scale >= 2^20 and retain that scale parameter.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

@[pl_fold] def numericalRationalPower : Exp rT := pl%
  fun scale a b exponent u,
    if (b <= #0) || (a < #0) then fail else
      &Occil.Numeric.coin scale
        (&Occil.Numeric.pow scale (scale * a / b) exponent) #()

/-- General positive-real m version of the lower-gamma ratio, using the source's
power-of-uniform proposal and decreasing-chain rejection on a finite grid. -/
@[pl_fold] def numericalLowerGammaRatio : Exp rT := pl%
  rec draw scale m x u :=
    if (scale <= #1) || (m <= #0) || (x < #0) || (scale < x) then fail else
      let proposal := &Occil.Numeric.uniform scale #();
      let value := &Occil.Numeric.pow scale proposal (&Occil.Numeric.div scale scale m);
      let chain := (rec decrease previous count :=
        let next := &Occil.Numeric.uniform scale #();
        if next < previous then decrease next (count + #1) else count);
      let count := chain value #0;
      if count % #2 = #0 then value < x else draw scale m x #()

/-- Finite-grid version of the fractional reciprocal identity for Euler's constant. -/
@[pl_fold] def numericalEulerReciprocal : Exp rT := pl%
  fun scale u,
    let uniform := &Occil.Numeric.uniform scale #();
    let reciprocal := &Occil.Numeric.div scale scale uniform;
    ~(&Occil.Numeric.coin scale (reciprocal % scale) #())

@[pl_fold] def numericalExpRationalProduct : Exp rT := pl%
  fun scale x y z t u,
    if (x < #0) || (y <= #0) || (z < #0) || (t <= #0) then fail else
      let exponent := -(scale * x / y);
      let probability := &Occil.Numeric.exp scale exponent * z / t;
      &Occil.Numeric.coin scale probability #()

@[pl_fold] def numericalLogPiOverPi : Exp rT := pl%
  fun scale u,
    let p := &Occil.Numeric.pi scale;
    &Occil.Numeric.coin scale
      (&Occil.Numeric.div scale (&Occil.Numeric.log scale p) p) #()

end Occil.Constants
