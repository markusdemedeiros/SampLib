import Samplers.Constants.Pi
import Samplers.Constants.Exponential
import Samplers.Continuous

/-!
# Special known-probability coins

Exact series, integral and rejection constructions for zeta, Euler's constant,
logarithms, error-function and lower-gamma ratios.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

/-- Exact 3*zeta(3)/4. Integral tail bound: sum_{k>n} k^-3 <=1/(2n²). -/
@[pl_fold] def threeZetaThreeOverFour : Exp rT := pl%
  fun u, &fromPositiveSeries (fun n,
    let k := n + #1;
    (#3, (#4 * k * k * k, (#3, #8 * k * k)))) #()

/-- Exact ζ(k)*(1-2^(1-k)), k>=2, by the k-fold geometric-bag integral.
The k latent uniforms persist across all iterations of the two-coin construction. -/
@[pl_fold] def zetaRelated : Exp rT := pl%
  fun k u,
    if k < #2 then fail else
      let create := (rec allocate remaining := if remaining = #0 then inl(#()) else
        let bag := &Occil.newUniformBag #();
        inr((bag, allocate (remaining - #1))));
      let bags := create k;
      let product := (rec all xs := case! xs
        | inl(v) => #true
        | inr(p) => if &Occil.sampleGeometricBag (fst(p)) #() then all (snd(p)) else #false);
      &Occil.oneDivOnePlus (fun v, product bags) #()

/-- Exact Euler–Mascheroni coin using the positive Sondow series and the
rational tail bound in Occil's presentation of Mendo's method. -/
@[pl_fold] def eulerMascheroni : Exp rT := pl%
  fun u,
    let bits := (rec count n := if n = #0 then #0 else #1 + count (n / #2));
    &fromPositiveSeries (fun n,
      if n = #0 then (#1, (#2, (#1, #2))) else
        let b := bits n;
        (b, (#2 * n * (#2 * n + #1) * (#2 * n + #2),
          ((#2 + b) * n + #1, #16 * n * n * n)))) #()

/-- Exact ln(1+x/y), 0<=x<=y. -/
@[pl_fold] def logOnePlusRational : Exp rT := pl%
  fun x y u, &Occil.logOnePlusFactory (fun v, &Occil.rationalCoin x y) #()

/-- Exact (a/b)^n for a rational base in [0,1] and integer n>=0. -/
@[pl_fold] def rationalIntegerPower : Exp rT := pl%
  fun a b n u,
    if n < #0 then fail else
      let loop := (rec draw remaining := if remaining = #0 then #true else
        if &Occil.rationalCoin a b then draw (remaining - #1) else #false);
      loop n

/-- Exact e/pi from independently calculated rational interval bounds. -/
@[pl_fold] def eOverPi : Exp rT := pl%
  fun u, &fromBounds (fun n,
    let e := &eBounds n;
    let p := &piBounds n;
    let eLow := fst(e);
    let eHigh := fst(snd(e));
    let eDenominator := snd(snd(e));
    let pLow := fst(p);
    let pHigh := fst(snd(p));
    let pDenominator := snd(snd(p));
    (eLow * pDenominator * pLow,
      (eHigh * pDenominator * pHigh, eDenominator * pLow * pHigh))) #()

/-- Exact erf(x)/erf(1), 0<=x<=1. Rejection uses maximum-of-two uniform
comparison values; no square, exp, or erf primitive is needed. -/
@[pl_fold] def erfRatio : Exp rT := pl%
  rec draw x u :=
    let value := urand;
    let chain := (rec decrease previous count :=
      let a := urand;
      let b := urand;
      let next := (if a < b then b else a);
      if next < previous then decrease next (count + #1) else count);
    let count := chain value #0;
    if count % #2 = #0 then value < x else draw x #()

/-- Exact gamma(m,x)/gamma(m,1) for integer m>0, x in [0,1]. -/
@[pl_fold] def lowerGammaIntegerRatio : Exp rT := pl%
  rec draw m x u :=
    if m <= #0 then fail else
      let value := &Occil.orderStatistic m m;
      let decreases := &Occil.decreasingTrial #0 value;
      if decreases % #2 = #0 then value < x else draw m x #()


end Occil.Constants
