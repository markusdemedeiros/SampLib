import Samplers.Numerical.Gamma
import Samplers.Discrete

/-!
Distribution families derived from gamma and beta variates.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

@[pl_fold] def chiSquared : Exp rT := pl%
  fun scale degrees u,
    if degrees <= #0 then fail else #2 * &gamma scale (&positiveGrid (degrees / #2)) scale #()

/-- Noncentral chi-square via a Poisson mixture; noncentrality is sum of mean squares. -/
@[pl_fold] def noncentralChiSquared : Exp rT := pl%
  fun scale degrees noncentrality u,
    if (degrees <= #0) || (noncentrality < #0) then fail else
      let count := &Occil.poissonRational noncentrality (#2 * scale);
      #2 * &gamma scale (&positiveGrid (degrees / #2 + count * scale)) scale #()

@[pl_fold] def studentT : Exp rT := pl%
  fun scale degrees shift u,
    if degrees <= #0 then fail else
      &Numeric.div scale (&normal scale shift scale #())
        (&Numeric.sqrt scale (&Numeric.div scale (&chiSquared scale degrees #()) degrees))

@[pl_fold] def fisherF : Exp rT := pl%
  fun scale numeratorDegrees denominatorDegrees noncentrality u,
    if (numeratorDegrees <= #0) || (denominatorDegrees <= #0) then fail else
      &Numeric.div scale
        (&Numeric.div scale (&chiSquared scale numeratorDegrees #()) numeratorDegrees)
        (&Numeric.div scale
          (&noncentralChiSquared scale denominatorDegrees noncentrality #()) denominatorDegrees)

@[pl_fold] def inverseGamma : Exp rT := pl%
  fun scale shape width u,
    if width <= #0 then fail else &Numeric.div scale width (&gamma scale shape scale #())

@[pl_fold] def kumaraswamy : Exp rT := pl%
  fun scale a b u,
    if a <= #0 then fail else
      &Numeric.pow scale (&beta scale scale b #()) (&Numeric.div scale scale a)

@[pl_fold] def betaPrime : Exp rT := pl%
  fun scale a b power u,
    if power <= #0 then fail else
      &Numeric.pow scale
        (&Numeric.div scale (&gamma scale a scale #()) (&gamma scale b scale #()))
        (&Numeric.div scale scale power)

@[pl_fold] def betaPERT : Exp rT := pl%
  fun scale lo mode hi shape u,
    if (hi <= lo) || (mode < lo) || (hi < mode) || (shape < #0) then fail else
      let a := scale + &Numeric.div scale (&Numeric.mul scale (mode - lo) shape) (hi - lo);
      let b := scale + &Numeric.div scale (&Numeric.mul scale (hi - mode) shape) (hi - lo);
      lo + &Numeric.mul scale (hi - lo) (&beta scale a b #())

@[pl_fold] def noncentralBeta : Exp rT := pl%
  fun scale a b noncentrality u,
    if noncentrality < #0 then fail else
      let n := &Occil.poissonRational noncentrality scale;
      &beta scale (a + n * scale) b #()

@[pl_fold] def chi : Exp rT := pl%
  fun scale degrees u, &Numeric.sqrt scale (&chiSquared scale degrees #())

@[pl_fold] def inverseChiSquared : Exp rT := pl%
  fun scale degrees u, &Numeric.div scale degrees (&chiSquared scale degrees #())

@[pl_fold] def levy : Exp rT := pl%
  fun scale location width u,
    if width <= #0 then fail else
      location + &Numeric.div scale width (#2 * &gamma scale (scale / #2) scale #())

@[pl_fold] def maxwell : Exp rT := pl%
  fun scale width u,
    if width <= #0 then fail else
      &Numeric.mul scale width (&Numeric.sqrt scale (#2 * &gamma scale (#3 * scale / #2) scale #()))

@[pl_fold] def wignerSemicircle : Exp rT := pl%
  fun scale center radius u,
    if radius <= #0 then fail else
      center + &Numeric.mul scale radius (#2 * &beta scale (#3 * scale / #2) (#3 * scale / #2) #() - scale)

@[pl_fold] def parabolic : Exp rT := pl%
  fun scale u, &beta scale (#2 * scale) (#2 * scale) #()

@[pl_fold] def arcsine : Exp rT := pl%
  fun scale u, &beta scale (scale / #2) (scale / #2) #()

/-- Generalized normal / exponential-power density proportional to exp(-|x|^shape). -/
@[pl_fold] def generalizedNormal : Exp rT := pl%
  fun scale shape location width u,
    if (shape <= #0) || (width <= #0) then fail else
      let reciprocal := &Numeric.div scale scale shape;
      let magnitude := &Numeric.pow scale (&gamma scale reciprocal scale #()) reciprocal;
      let signed := (if &Occil.fairCoin #() then magnitude else -magnitude);
      location + &Numeric.mul scale width signed

@[pl_fold] def generalizedGamma : Exp rT := pl%
  fun scale shape power location width u,
    if (power = #0) || (width <= #0) then fail else
      location + &Numeric.mul scale width
        (&Numeric.pow scale (&gamma scale shape scale #()) (&Numeric.div scale scale power))

@[pl_fold] def generalizedInverseGamma : Exp rT := pl%
  fun scale shape power location width u,
    &Numeric.div scale scale (&generalizedGamma scale shape power location width #())

/-- Main-index power distribution: Beta(shape,1)/domain; domain is an inverse scale. -/
@[pl_fold] def powerDistribution : Exp rT := pl%
  fun scale shape domain u,
    if domain <= #0 then fail else &Numeric.div scale (&beta scale shape scale #()) domain

/-- Twin-t rejection. The index omits the square root in its acceptance denominator;
this uses y+sqrt(1+y^2), as required by the named twin-t density. -/
@[pl_fold] def twinT : Exp rT := pl%
  rec draw scale degrees u :=
    let x := &studentT scale degrees #0 #();
    let y := &Numeric.div scale (&Numeric.mul scale x x) degrees;
    let accept := &Numeric.pow scale
      (&Numeric.div scale (scale + y)
        (y + &Numeric.sqrt scale (scale + &Numeric.mul scale y y)))
      ((degrees + scale) / #2);
    if &Numeric.coin scale accept #() then x else draw scale degrees #()

/-- Power-function distribution on [0,width], as listed in randmisc.html. -/
@[pl_fold] def powerFunction : Exp rT := pl%
  fun scale shape width u,
    if width <= #0 then fail else &Numeric.mul scale width (&beta scale shape scale #())

/-- Gamma-mixture names appearing in the main distribution index. -/
@[pl_fold] def stacy : Exp rT := pl%
  fun scale shape power width u, &generalizedGamma scale shape power #0 width #()

@[pl_fold] def amoroso : Exp rT := pl%
  fun scale shape power location width u, &generalizedGamma scale shape power location width #()

@[pl_fold] def pearsonVI : Exp rT := pl%
  fun scale a b u, &betaPrime scale a b scale #()

@[pl_fold] def singhMaddala : Exp rT := pl%
  fun scale shape power u, &betaPrime scale scale shape power #()

@[pl_fold] def dagum : Exp rT := pl%
  fun scale shape power u, &betaPrime scale shape scale power #()

@[pl_fold] def logLogistic : Exp rT := pl%
  fun scale power u, &betaPrime scale scale scale power #()

/-- Minimum and maximum of a positive integer number of independent uniforms. -/
@[pl_fold] def minUniform : Exp rT := pl%
  fun scale count u, if count <= #0 then fail else &beta scale scale (count * scale) #()

@[pl_fold] def maxUniform : Exp rT := pl%
  fun scale count u, if count <= #0 then fail else &beta scale (count * scale) scale #()

end Occil.Numerical
