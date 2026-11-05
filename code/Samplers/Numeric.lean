import Samplers.Uniform

/-!
# Integer fixed-point arithmetic inside ProbLang

`x` represents the real number `x / scale`; the positive integer scale is an
explicit first argument. These are numerical approximations, not ideal-real
operations. All calculations, including series and range reduction, run in the
object language using unbounded integers. No FFI or host numerical oracle is used.

Elementary functions work with 24 guard bits and round toward zero on return.
Increasing scale improves the grid resolution; it does not turn these routines
into certified interval arithmetic. Pi and log(2) constants have 36 decimal digits.
Normal CDF uses the standard five-coefficient normal-tail approximation (roughly
1.5e-7 absolute analytic error) and quantiles invert that approximation.
-/
namespace Occil.Numeric

open ProbLang
variable {rT : Type _}

/-- Integer absolute value, without fixed-point rescaling. -/
@[pl_fold] def abs : Exp rT := pl%
  fun x, if x < #0 then -x else x

/-- Signed quotient rounded toward zero; the divisor must be positive. -/
@[pl_fold] def quotient : Exp rT := pl%
  fun x denominator,
    if denominator <= #0 then fail else
    if x < #0 then -((-x) / denominator) else x / denominator

@[pl_fold] def mul : Exp rT := pl%
  fun scale x y, &quotient (x * y) scale

@[pl_fold] def div : Exp rT := pl%
  fun scale x y,
    if (scale <= #0) || (y = #0) then fail else
    if y < #0 then &quotient (-(x * scale)) (-y)
    else &quotient (x * scale) y

/-- Pi rounded down onto the requested grid. -/
@[pl_fold] def pi : Exp rT := pl%
  fun scale,
    if scale <= #0 then fail else
    scale * #3141592653589793238462643383279502884 /
      #1000000000000000000000000000000000000

/-- Natural logarithm of 2 rounded down onto the requested grid. -/
@[pl_fold] def logTwo : Exp rT := pl%
  fun scale,
    if scale <= #0 then fail else
    scale * #693147180559945309417232121458176568 /
      #1000000000000000000000000000000000000

/-- Floor of sqrt(scale*x), hence a Q(scale) square root within one grid unit. -/
@[pl_fold] def sqrt : Exp rT := pl%
  fun scale x,
    if (scale <= #0) || (x < #0) then fail else
    let value := scale * x;
    if value = #0 then #0 else
      let iterate := (rec refine estimate :=
        let next := (estimate + value / estimate) / #2;
        if estimate <= next then estimate else refine next);
      iterate value

/-- Exp at the supplied working scale: halve into [-1/2,1/2], evaluate its
Taylor series until terms round to zero, then undo halving by squaring. -/
@[pl_fold] def expRaw : Exp rT := pl%
  fun scale x,
    let series := (fun argument,
      let sum := (rec addTerm k term total :=
        let next := &quotient (term * argument) (scale * k);
        if next = #0 then total else addTerm (k + #1) next (total + next));
      sum #1 scale scale);
    let square := (rec repeatSquare n value :=
      if n = #0 then value else
        repeatSquare (n - #1) (&mul scale value value));
    let reduce := (rec halve argument count :=
      if scale < #2 * &abs argument then
        halve (&quotient argument #2) (count + #1)
      else square count (series argument));
    reduce x #0

@[pl_fold] def exp : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      &quotient (&expRaw (scale * #16777216) (x * #16777216)) #16777216

/-- Log at working precision: normalize to [1,2), then use
log(z)=2*(y+y^3/3+...), y=(z-1)/(z+1). -/
@[pl_fold] def logRaw : Exp rT := pl%
  fun scale x,
    let series := (fun argument,
      let y := &div scale (argument - scale) (argument + scale);
      let square := &mul scale y y;
      let sum := (rec addTerm odd term total :=
        let next := &mul scale term square;
        if next = #0 then #2 * total else
          addTerm (odd + #2) next (total + next / (odd + #2)));
      sum #1 y y);
    let normalize := (rec reduce argument exponent :=
      if argument < scale then reduce (argument * #2) (exponent - #1) else
      if #2 * scale <= argument then reduce (argument / #2) (exponent + #1) else
        series argument + exponent * &logTwo scale);
    normalize x #0

@[pl_fold] def log : Exp rT := pl%
  fun scale x,
    if (scale <= #0) || (x <= #0) then fail else
      &quotient (&logRaw (scale * #16777216) (x * #16777216)) #16777216

/-- Real exponentiation for nonnegative bases. Convention: 0^0=1;
zero to a negative exponent and negative bases are rejected. -/
@[pl_fold] def pow : Exp rT := pl%
  fun scale x exponent,
    if (scale <= #0) || (x < #0) then fail else
    if exponent = #0 then scale else
    if x = #0 then if exponent < #0 then fail else #0 else
      let workScale := scale * #16777216;
      let logarithm := &logRaw workScale (x * #16777216);
      let argument := &mul workScale logarithm (exponent * #16777216);
      &quotient (&expRaw workScale argument) #16777216

/-- Reduce an angle to [-pi,pi) at the working scale. -/
@[pl_fold] def reduceAngle : Exp rT := pl%
  fun scale x,
    let halfTurn := &pi scale;
    (x + halfTurn) % (#2 * halfTurn) - halfTurn

@[pl_fold] def sinRaw : Exp rT := pl%
  fun scale x,
    let angle := &reduceAngle scale x;
    let square := &mul scale angle angle;
    let series := (rec addTerm n term total :=
      let denominator := scale * (#2 * n) * (#2 * n + #1);
      let next := &quotient (-(term * square)) denominator;
      if next = #0 then total else addTerm (n + #1) next (total + next));
    series #1 angle angle

@[pl_fold] def cosRaw : Exp rT := pl%
  fun scale x,
    let angle := &reduceAngle scale x;
    let square := &mul scale angle angle;
    let series := (rec addTerm n term total :=
      let denominator := scale * (#2 * n - #1) * (#2 * n);
      let next := &quotient (-(term * square)) denominator;
      if next = #0 then total else addTerm (n + #1) next (total + next));
    series #1 scale scale

@[pl_fold] def sin : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      &quotient (&sinRaw (scale * #16777216) (x * #16777216)) #16777216

@[pl_fold] def cos : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      &quotient (&cosRaw (scale * #16777216) (x * #16777216)) #16777216

/-- Tangent; rejects arguments whose rounded cosine is zero. -/
@[pl_fold] def tan : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      let workScale := scale * #16777216;
      let numerator := &sinRaw workScale (x * #16777216);
      let denominator := &cosRaw workScale (x * #16777216);
      &quotient (&div workScale numerator denominator) #16777216

/-- Arctangent's power series, used only on arguments of magnitude <=1/2. -/
@[pl_fold] def atanSeries : Exp rT := pl%
  fun scale x,
    let square := &mul scale x x;
    let sum := (rec addTerm odd term total :=
      let next := -(&mul scale term square);
      if next = #0 then total else
        addTerm (odd + #2) next (total + &quotient next (odd + #2)));
    sum #1 x x

@[pl_fold] def atanRaw : Exp rT := pl%
  fun scale x,
    let positive := (rec evaluate argument :=
      if scale < argument then
        &pi scale / #2 - evaluate (&div scale scale argument)
      else if scale < #2 * argument then
        &atanSeries scale (scale / #2) +
          &atanSeries scale (&div scale (#2 * argument - scale) (#2 * scale + argument))
      else &atanSeries scale argument);
    if x < #0 then -(positive (-x)) else positive x

@[pl_fold] def atan : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      &quotient (&atanRaw (scale * #16777216) (x * #16777216)) #16777216

/-- Standard normal CDF at working precision, using a five-term tail fit.
The absolute approximation error does not vanish merely by increasing scale. -/
@[pl_fold] def normalCDFRaw : Exp rT := pl%
  fun scale x,
    let magnitude := &abs x;
    let t := &div scale scale (scale + magnitude * #2316419 / #10000000);
    let b1 := scale * #319381530 / #1000000000;
    let b2 := -(scale * #356563782 / #1000000000);
    let b3 := scale * #1781477937 / #1000000000;
    let b4 := -(scale * #1821255978 / #1000000000);
    let b5 := scale * #1330274429 / #1000000000;
    let polynomial := &mul scale t
      (b1 + &mul scale t
        (b2 + &mul scale t
          (b3 + &mul scale t (b4 + &mul scale t b5))));
    let density := &mul scale
      (&expRaw scale (-(&mul scale magnitude magnitude) / #2))
      (scale * #398942280401432677 / #1000000000000000000);
    let tail := &mul scale density polynomial;
    let value := (if x < #0 then tail else scale - tail);
    if value < #0 then #0 else if scale < value then scale else value

@[pl_fold] def normalCDF : Exp rT := pl%
  fun scale x,
    if scale <= #0 then fail else
      &quotient (&normalCDFRaw (scale * #16777216) (x * #16777216)) #16777216

/-- Quantile of the approximate standard normal CDF, by bracketed bisection.
Requires 0<p<scale; returns a fixed-point integer. -/
@[pl_fold] def normalQuantile : Exp rT := pl%
  fun scale probability,
    if (scale <= #0) || (probability <= #0) || (scale <= probability) then fail else
      let bisect := (rec search lower upper :=
        if upper - lower <= #1 then lower else
          let middle := (lower + upper) / #2;
          if &normalCDF scale middle < probability then search middle upper
          else search lower middle);
      let bracket := (rec widen bound :=
        if (&normalCDF scale (-bound) <= probability) &&
            (probability <= &normalCDF scale bound) then bisect (-bound) bound
        else widen (bound * #2));
      bracket (#8 * scale)

/-- Interior grid uniform: integers 1,...,scale-1. -/
@[pl_fold] def uniform : Exp rT := pl%
  fun scale u,
    if scale <= #1 then fail else #1 + &Occil.uniformInt (scale - #1)

/-- Bernoulli on a Q(scale) probability. -/
@[pl_fold] def coin : Exp rT := pl%
  fun scale probability u, &Occil.rationalCoin probability scale

end Occil.Numeric
