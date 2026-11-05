import Samplers.Numerical.Core

/-!
Inverse transforms and elementary scalar distribution constructions.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

@[pl_fold] def laplace : Exp rT := pl%
  fun scale mean width u,
    let x := &exponential scale scale #();
    let signed := (if &Occil.fairCoin #() then x else -x);
    if width <= #0 then fail else mean + &Numeric.mul scale width signed

@[pl_fold] def logistic : Exp rT := pl%
  fun scale mean width u,
    if width <= #0 then fail else
      let x := &Numeric.uniform scale #();
      let z := &Numeric.log scale x - &Numeric.log scale (scale - x);
      mean + &Numeric.mul scale width z

@[pl_fold] def cauchy : Exp rT := pl%
  fun scale location width u,
    if width <= #0 then fail else
      let angle := &Numeric.mul scale (&Numeric.pi scale)
        (&Numeric.uniform scale #() - scale / #2);
      location + &Numeric.mul scale width (&Numeric.tan scale angle)

/-- The first-quadrant disk ratio alternative listed under Cauchy. -/
@[pl_fold] def cauchyDisk : Exp rT := pl%
  rec draw scale location width u :=
    if width <= #0 then fail else
      let x := &Numeric.uniform scale #();
      let y := &Numeric.uniform scale #();
      if scale < &Numeric.mul scale x x + &Numeric.mul scale y y then
        draw scale location width #()
      else
        let ratio := &Numeric.div scale y x;
        let signed := (if &Occil.fairCoin #() then ratio else -ratio);
        location + &Numeric.mul scale width signed

@[pl_fold] def weibull : Exp rT := pl%
  fun scale shape width u,
    if (shape <= #0) || (width <= #0) then fail else
      &Numeric.mul scale width (&Numeric.pow scale (&exponential scale scale #())
        (&Numeric.div scale scale shape))

@[pl_fold] def pareto : Exp rT := pl%
  fun scale shape minimum u,
    if (shape <= #0) || (minimum <= #0) then fail else
      &Numeric.mul scale minimum (&Numeric.pow scale (&Numeric.uniform scale #())
        (-(&Numeric.div scale scale shape)))

@[pl_fold] def rayleigh : Exp rT := pl%
  fun scale width u,
    if width <= #0 then fail else
      &Numeric.mul scale width (&Numeric.sqrt scale (#2 * &exponential scale scale #()))

@[pl_fold] def gumbel : Exp rT := pl%
  fun scale location width u,
    if width <= #0 then fail else
      location - &Numeric.mul scale width (&Numeric.log scale (&exponential scale scale #()))

/-- GEV parameterization used in Occil's index: (E^(-shape)-1)/shape. -/
@[pl_fold] def generalizedExtremeValue : Exp rT := pl%
  fun scale shape location width u,
    if width <= #0 then fail else
    if shape = #0 then &gumbel scale location width #() else
      let value := &Numeric.div scale
        (&Numeric.pow scale (&exponential scale scale #()) (-shape) - scale) shape;
      location + &Numeric.mul scale width value

@[pl_fold] def frechet : Exp rT := pl%
  fun scale shape minimum width u,
    if (shape <= #0) || (width <= #0) then fail else
      minimum + &Numeric.mul scale width (&Numeric.pow scale
        (&exponential scale scale #()) (-(&Numeric.div scale scale shape)))

/-- Triangular on [lo,hi], with mode between the endpoints. -/
@[pl_fold] def triangular : Exp rT := pl%
  fun scale lo mode hi u,
    if (hi <= lo) || (mode < lo) || (hi < mode) then fail else
      let x := &Numeric.uniform scale #();
      let split := &Numeric.div scale (mode - lo) (hi - lo);
      if x < split then lo + &Numeric.sqrt scale
        (&Numeric.mul scale x (&Numeric.mul scale (hi - lo) (mode - lo)))
      else hi - &Numeric.sqrt scale
        (&Numeric.mul scale (scale - x) (&Numeric.mul scale (hi - lo) (hi - mode)))

/-- Stein–Keblis family (1-alpha)*min(U,V)+alpha*max(U,V), alpha in [0,1]. -/
@[pl_fold] def triangularUniforms : Exp rT := pl%
  fun scale alpha u,
    if (alpha < #0) || (scale < alpha) then fail else
      let x := &Numeric.uniform scale #();
      let y := &Numeric.uniform scale #();
      let low := (if x < y then x else y);
      let high := (if x < y then y else x);
      &Numeric.mul scale (scale - alpha) low + &Numeric.mul scale alpha high

@[pl_fold] def tukeyLambda : Exp rT := pl%
  fun scale shape u,
    let x := &Numeric.uniform scale #();
    if shape = #0 then &Numeric.log scale x - &Numeric.log scale (scale - x)
    else &Numeric.div scale
      (&Numeric.pow scale x shape - &Numeric.pow scale (scale - x) shape) shape

@[pl_fold] def generalizedTukeyLambda : Exp rT := pl%
  fun scale leftShape rightShape leftWidth rightWidth location u,
    let x := &Numeric.uniform scale #();
    let left := (if leftShape = #0 then &Numeric.log scale x else
      &Numeric.div scale (&Numeric.pow scale x leftShape - scale) leftShape);
    let right := (if rightShape = #0 then &Numeric.log scale (scale - x) else
      &Numeric.div scale (&Numeric.pow scale (scale - x) rightShape - scale) rightShape);
    location + &Numeric.mul scale leftWidth left - &Numeric.mul scale rightWidth right

/-- Ordinary power law on a finite positive interval, with density proportional to x^exponent. -/
@[pl_fold] def powerLaw : Exp rT := pl%
  fun scale lo hi exponent u,
    if (lo <= #0) || (hi <= lo) then fail else
      let power := exponent + scale;
      if power = #0 then
        &Numeric.exp scale (&uniformRange scale (&Numeric.log scale lo) (&Numeric.log scale hi) #())
      else
        let a := &Numeric.pow scale lo power;
        let b := &Numeric.pow scale hi power;
        let x := a + &Numeric.mul scale (b - a) (&Numeric.uniform scale #());
        &Numeric.pow scale x (&Numeric.div scale scale power)

@[pl_fold] def logarithmicProduct : Exp rT := pl%
  fun scale u, &Numeric.mul scale (&Numeric.uniform scale #()) (&Numeric.uniform scale #())

@[pl_fold] def doubleLogarithmic : Exp rT := pl%
  fun scale u,
    let magnitude := &logarithmicProduct scale #() / #2;
    if &Occil.fairCoin #() then scale / #2 + magnitude else scale / #2 - magnitude

@[pl_fold] def bates : Exp rT := pl%
  fun scale count u,
    if count <= #0 then fail else
      let loop := (rec sum remaining total := if remaining = #0 then total else
        sum (remaining - #1) (total + &Numeric.uniform scale #()));
      loop count #0 / count

end Occil.Numerical
