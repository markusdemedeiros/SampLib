import Samplers.Numerical
import Samplers.Continuous

/-!
Specialized numerical scalar laws and elementary uniform transformations.

Real-valued inputs and outputs are Q(scale) integers. Tulap's geometric counts
are ordinary integers internally; its returned value is fixed point. Numerical
transformations and rejection loops execute entirely inside ProbLang.
-/
namespace Occil.Specialized

open ProbLang

variable {rT : Type _}

/-- Hyperbolic secant density sech(x)/pi, by numerical inversion. -/
@[pl_fold] def hyperbolicSecant : Exp rT := pl%
  fun scale u,
    let angle := &Numeric.mul scale (&Numeric.pi scale) (&Numeric.uniform scale #()) / #2;
    &Numeric.log scale (&Numeric.tan scale angle)

/-- Devroye–Györfi's three-uniform Epanechnikov construction on [-1,1]. -/
@[pl_fold] def epanechnikov : Exp rT := pl%
  fun scale u,
    let a := &Numeric.uniform scale #();
    let b := &Numeric.uniform scale #();
    let c := &Numeric.uniform scale #();
    let magnitude := (if (a < c) && (b < c) then b else c);
    if &Occil.fairCoin #() then magnitude else -magnitude

@[pl_fold] def ratioUniforms : Exp rT := pl%
  fun scale u,
    &Numeric.div scale (&Numeric.uniform scale #()) (&Numeric.uniform scale #())

@[pl_fold] def reciprocalUniform : Exp rT := pl%
  fun scale u, &Numeric.div scale scale (&Numeric.uniform scale #())

@[pl_fold] def reciprocalPowerUniform : Exp rT := pl%
  fun scale power u,
    if power <= #0 then fail else
      &Numeric.pow scale (&Numeric.uniform scale #()) (-(&Numeric.div scale scale power))

@[pl_fold] def uniformOdds : Exp rT := pl%
  fun scale u,
    let x := &Numeric.uniform scale #();
    &Numeric.div scale x (scale - x)

/-- CDF 1-cos(pi*x/2), x in [0,1], inverted with atan and sqrt. -/
@[pl_fold] def arcCosine : Exp rT := pl%
  fun scale u,
    let x := &Numeric.uniform scale #();
    let numerator := &Numeric.sqrt scale (scale - &Numeric.mul scale x x);
    &Numeric.div scale (#2 * &Numeric.atan scale (&Numeric.div scale numerator x))
      (&Numeric.pi scale)

@[pl_fold] def exponentialLogRate : Exp rT := pl%
  fun scale base u,
    if base <= scale then fail else
      &Numerical.exponential scale (&Numeric.log scale base) #()

/-- Integer exponent, used for the exact-grid discrete-Laplace CDF. -/
@[pl_fold] def integerPower : Exp rT := pl%
  fun scale base exponent,
    if exponent < #0 then fail else
      let loop := (rec multiply n accumulator := if n = #0 then accumulator else
        multiply (n - #1) (&Numeric.mul scale accumulator base));
      loop exponent scale

/-- CDF of G1-G2+Uniform(-1/2,1/2), with P(G=k)=(1-b)b^k. -/
@[pl_fold] def tulapCDF : Exp rT := pl%
  fun scale b x,
    if (b <= #0) || (scale <= b) then fail else
      let n := (x + scale / #2) / scale;
      let fraction := x - n * scale + scale / #2;
      let absolute := &Numeric.abs n;
      let mass := &Numeric.mul scale (&Numeric.div scale (scale - b) (scale + b))
        (&integerPower scale b absolute);
      let base := (if n <= #0 then
        &Numeric.div scale (&integerPower scale b (#1 - n)) (scale + b)
      else scale - &Numeric.div scale (&integerPower scale b n) (scale + b));
      base + &Numeric.mul scale fraction mass

/-- Tulap(location,b,q). q in [0,1) trims q/2 probability from each tail. -/
@[pl_fold] def tulap : Exp rT := pl%
  rec draw scale location b q u :=
    if (b <= #0) || (scale <= b) || (q < #0) || (scale <= q) then fail else
      let coin := (fun u, &Numeric.coin scale b #());
      let first := &Occil.geometricFailures coin #0;
      let second := &Occil.geometricFailures coin #0;
      let x := (second - first) * scale + &Numeric.uniform scale #() - scale / #2;
      let probability := &tulapCDF scale b x;
      if (probability < q / #2) || (scale - q / #2 < probability) then
        draw scale location b q #()
      else location + x

/-- Continuous Bernoulli by numerical inverse CDF; endpoints are limiting atoms. -/
@[pl_fold] def continuousBernoulli : Exp rT := pl%
  fun scale probability u,
    if (probability < #0) || (scale < probability) then fail else
    if probability = #0 then #0 else if probability = scale then scale else
      let uniform := &Numeric.uniform scale #();
      if #2 * probability = scale then uniform else
        let odds := &Numeric.div scale probability (scale - probability);
        let denominator := &Numeric.log scale odds;
        if denominator = #0 then uniform else
          &Numeric.div scale
            (&Numeric.log scale (scale + &Numeric.mul scale uniform (odds - scale))) denominator

@[pl_fold] def powerFunction : Exp rT := pl%
  fun scale shape width u,
    if (shape <= #0) || (width <= #0) then fail else
      &Numeric.mul scale width (&Numeric.pow scale (&Numeric.uniform scale #())
        (&Numeric.div scale scale shape))

@[pl_fold] def lehmannWeibull : Exp rT := pl%
  fun scale firstShape secondShape rate u,
    if (firstShape <= #0) || (secondShape <= #0) then fail else
      &Numeric.div scale
        (&Numeric.pow scale (&Numerical.exponential scale rate #())
          (&Numeric.div scale scale firstShape)) secondShape

@[pl_fold] def marshallOlkin : Exp rT := pl%
  fun scale alpha u,
    if (alpha < #0) || (scale < alpha) then fail else
      let x := &Numeric.uniform scale #();
      &Numeric.div scale (scale - x) (scale + &Numeric.mul scale x (alpha - scale))

@[pl_fold] def slash : Exp rT := pl%
  fun scale power u,
    if power <= #0 then fail else
      &Numeric.div scale (&Numerical.normal scale #0 scale #())
        (&Numeric.pow scale (&Numeric.uniform scale #()) (&Numeric.div scale scale power))

@[pl_fold] def lomax : Exp rT := pl%
  fun scale shape u,
    if shape <= #0 then fail else
      &Numeric.pow scale (&Numeric.uniform scale #()) (-(&Numeric.div scale scale shape)) - scale

@[pl_fold] def powerLomax : Exp rT := pl%
  fun scale alpha beta u,
    if beta <= #0 then fail else
      &Numeric.pow scale (&lomax scale alpha #()) (&Numeric.div scale scale beta)

@[pl_fold] def toppLeone : Exp rT := pl%
  fun scale alpha u,
    if alpha <= #0 then fail else
      scale - &Numeric.sqrt scale
        (scale - &Numeric.pow scale (&Numeric.uniform scale #()) (&Numeric.div scale scale alpha))

@[pl_fold] def generalizedPareto : Exp rT := pl%
  fun scale width shape u,
    if (width <= #0) || (shape <= #0) then fail else
      &Numeric.mul scale width (&Numeric.div scale
        (&Numeric.pow scale (&reciprocalUniform scale #()) shape - scale) shape)

/-- Uniform numerical point in a quarter rectellipse; radii are fixed point,
    squareness lies in [0,1]. Squareness 0 gives an ellipse, 1 a rectangle. -/
@[pl_fold] def quarterRectellipse : Exp rT := pl%
  rec draw scale horizontalRadius verticalRadius squareness u :=
    if (horizontalRadius <= #0) || (verticalRadius <= #0) ||
      (squareness < #0) || (scale < squareness) then fail else
      let x := &Numeric.uniform scale #();
      let y := &Numeric.uniform scale #();
      let xSquared := &Numeric.mul scale x x;
      let ySquared := &Numeric.mul scale y y;
      let cross := &Numeric.mul scale (&Numeric.mul scale squareness squareness)
        (&Numeric.mul scale xSquared ySquared);
      if #0 <= scale - xSquared - ySquared + cross then
        (&Numeric.mul scale horizontalRadius x, &Numeric.mul scale verticalRadius y)
      else draw scale horizontalRadius verticalRadius squareness #()

@[pl_fold] def rectellipse : Exp rT := pl%
  fun scale horizontalRadius verticalRadius squareness u,
    let p := &quarterRectellipse scale horizontalRadius verticalRadius squareness #();
    let x := (if &Occil.fairCoin #() then fst(p) else -(fst(p)));
    let y := (if &Occil.fairCoin #() then snd(p) else -(snd(p)));
    (x, y)

/-- Main-index cosine distribution on [-1/2,1/2], via asin(U)/pi.
atan(x/sqrt(1-x^2)) is the source's inverse-sine transformation. -/
@[pl_fold] def cosine : Exp rT := pl%
  fun scale u,
    let magnitude := &Numeric.uniform scale #();
    let x := (if &Occil.fairCoin #() then magnitude else -magnitude);
    let denominator := &Numeric.sqrt scale (scale - &Numeric.mul scale x x);
    &Numeric.div scale (&Numeric.atan scale (&Numeric.div scale x denominator))
      (&Numeric.pi scale)

end Occil.Specialized
