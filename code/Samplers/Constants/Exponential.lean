import Samplers.Constants.Engines

/-!
# Exponential probability constants

Exact factorial-series bounds and continued fractions generate coins involving
e and rational exponentials. Valid probability domains remain caller preconditions.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

/-- e in (lower/denominator,upper/denominator), via its factorial series. -/
@[pl_fold] def eBounds : Exp rT := pl%
  fun n,
    let last := n + #1;
    let sum := (rec addTerm k numerator denominator :=
      if k = last then
        (k * numerator, (k * numerator + #1, k * denominator))
      else
        let next := k + #1;
        addTerm next (numerator * next + #1) (denominator * next));
    sum #0 #1 #1

@[pl_fold] def eMinusTwo : Exp rT := pl%
  fun u, &fromBounds (fun n,
    let interval := &eBounds n;
    let d := snd(snd(interval));
    ((fst(interval)) - #2 * d, (fst(snd(interval)) - #2 * d, d))) #()

/-- Exact Bernoulli(e*numerator/denominator), provided the result lies in [0,1]. -/
@[pl_fold] def eScaled : Exp rT := pl%
  fun numerator denominator u,
    if (numerator < #0) || (denominator <= #0) then fail else
      &fromBounds (fun n,
        let interval := &eBounds n;
        let low := fst(interval);
        let high := fst(snd(interval));
        let d := snd(snd(interval));
        (numerator * low, (numerator * high, denominator * d))) #()

@[pl_fold] def eDivThree : Exp rT := pl% fun u, &eScaled #1 #3 #()

@[pl_fold] def threeMinusE : Exp rT := pl%
  fun u, &fromBounds (fun n,
    let interval := &eBounds n;
    let d := snd(snd(interval));
    (#3 * d - fst(snd(interval)), (#3 * d - (fst(interval)), d))) #()

/-- Exact 1/(e+c-2), for integer c>=1. -/
@[pl_fold] def inverseEPlus : Exp rT := pl%
  fun c u,
    if c < #1 then fail else
      &fromBounds (fun n,
        let interval := &eBounds n;
        let d := snd(snd(interval));
        let lo := (fst(interval)) + (c - #2) * d;
        let hi := fst(snd(interval)) + (c - #2) * d;
        (d * lo, (d * hi, lo * hi))) #()

/-- Exact 1/(e+c-2) for rational c=numerator/denominator>=1. -/
@[pl_fold] def inverseEPlusRational : Exp rT := pl%
  fun numerator denominator u,
    if (denominator <= #0) || (numerator < denominator) then fail else
      &fromBounds (fun n,
        let interval := &eBounds n;
        let d := snd(snd(interval));
        let lo := fst(interval) * denominator + (numerator - #2 * denominator) * d;
        let hi := fst(snd(interval)) * denominator + (numerator - #2 * denominator) * d;
        (denominator * d * lo, (denominator * d * hi, lo * hi))) #()

/-- The article's continued-fraction expansion of 1/(e+c-2).
Position two is the alternate expansion for e-2. -/
@[pl_fold] def eContinuedFraction : Exp rT := pl%
  rec draw cNumerator cDenominator position :=
    if (cDenominator <= #0) || (cNumerator < cDenominator) || (position <= #0) then fail else
      let a := (if position = #1 then cNumerator else
        if position % #3 = #0 then #2 * (position / #3) else #1);
      let d := (if position = #1 then cDenominator else #1);
      if &Occil.rationalCoin a (a + d) then &Occil.rationalCoin d a else
      if draw cNumerator cDenominator (position + #1) then #false
      else draw cNumerator cDenominator position

@[pl_fold] def inverseEPlusContinuedFraction : Exp rT := pl%
  fun numerator denominator u, &eContinuedFraction numerator denominator #1

@[pl_fold] def eMinusTwoContinuedFraction : Exp rT := pl%
  fun u, &eContinuedFraction #1 #1 #2

/-- Exact tanh(1/2)=(e-1)/(e+1). -/
@[pl_fold] def tanhHalf : Exp rT := pl%
  fun u, &fromBounds (fun n,
    let interval := &eBounds n;
    let lo := (fst(interval));
    let hi := fst(snd(interval));
    let d := snd(snd(interval));
    ((lo - d) * (hi + d), ((hi - d) * (lo + d), (lo + d) * (hi + d)))) #()

/-- Exact alternating Taylor bounds for exp(-x/y), x>=0,y>0. The
truncation index is beyond x/y, so the remaining terms decrease in magnitude. -/
@[pl_fold] def expMinusBounds : Exp rT := pl%
  fun x y n,
    if (x < #0) || (y <= #0) || (n < #0) then fail else
      let last := x / y + #2 * n + #1;
      let sum := (rec addTerm k power numerator denominator :=
        let next := k + #1;
        let factor := y * next;
        let nextPower := -(power * x);
        let middle := numerator * factor;
        let nextDenominator := denominator * factor;
        if k = last then
          if nextPower < #0 then (middle + nextPower, (middle, nextDenominator))
          else (middle, (middle + nextPower, nextDenominator))
        else addTerm next nextPower (middle + nextPower) nextDenominator);
      sum #0 #1 #1 #1

/-- Exact exp(-x/y)*z/t, x,z>=0,y,t>0, on its valid probability domain.
The rational interval engine also supports the compensated case z>t. -/
@[pl_fold] def exponentialRationalProduct : Exp rT := pl%
  fun x y z t u,
    if (x < #0) || (y <= #0) || (z < #0) || (t <= #0) then fail else
      &fromBounds (fun n,
        let interval := &expMinusBounds x y n;
        let low := fst(interval);
        let high := fst(snd(interval));
        let d := snd(snd(interval));
        (z * low, (z * high, t * d))) #()

@[pl_fold] def eQuarter : Exp rT := pl% fun u, &eScaled #1 #4 #()

end Occil.Constants
