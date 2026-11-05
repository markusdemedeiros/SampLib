import Samplers.Constants.Engines

/-!
# Pi and arctangent probability constants

Machin's formula supplies exact rational bounds. The affine, reciprocal and
related constructions retain the probability domains stated in their docstrings.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

/-- Exact alternating-series enclosure of arctan(1/q), q>=2, after n>=1 terms. -/
@[pl_fold] def arctanReciprocalBounds : Exp rT := pl%
  fun q n,
    if (q < #2) || (n <= #0) then fail else
      let sum := (rec addTerm k power numerator denominator :=
        let termDenominator := (#2 * k + #1) * power;
        if k = n then
          let middle := numerator * termDenominator;
          let commonDenominator := denominator * termDenominator;
          if k % #2 = #0 then (middle, (middle + denominator, commonDenominator))
          else (middle - denominator, (middle, commonDenominator))
        else
          let sign := (if k % #2 = #0 then #1 else #(-1));
          addTerm (k + #1) (power * q * q)
            (numerator * termDenominator + sign * denominator)
            (denominator * termDenominator));
      sum #0 q #0 #1

/-- Exact Machin enclosure pi=16 atan(1/5)-4 atan(1/239). -/
@[pl_fold] def piBounds : Exp rT := pl%
  fun n,
    let a := &arctanReciprocalBounds #5 (n + #1);
    let b := &arctanReciprocalBounds #239 (n + #1);
    let aLower := (fst(a));
    let aUpper := fst(snd(a));
    let aDenominator := snd(snd(a));
    let bLower := (fst(b));
    let bUpper := fst(snd(b));
    let bDenominator := snd(snd(b));
    (#16 * aLower * bDenominator - #4 * bUpper * aDenominator,
      (#16 * aUpper * bDenominator - #4 * bLower * aDenominator,
        aDenominator * bDenominator))

/-- Bernoulli((pi-offset)/divisor); parameters must put the result in [0,1]. -/
@[pl_fold] def piAffine : Exp rT := pl%
  fun offset divisor u,
    if divisor <= #0 then fail else
      &fromBounds (fun n,
        let interval := &piBounds n;
        let d := snd(snd(interval));
        ((fst(interval)) - offset * d,
          (fst(snd(interval)) - offset * d, divisor * d))) #()

@[pl_fold] def piQuarter : Exp rT := pl% fun u, &piAffine #0 #4 #()

@[pl_fold] def piTwelfth : Exp rT := pl% fun u, &piAffine #0 #12 #()

@[pl_fold] def piQuarterMinusHalf : Exp rT := pl% fun u, &piAffine #2 #4 #()

@[pl_fold] def piMinusThreeOverFour : Exp rT := pl% fun u, &piAffine #3 #4 #()

@[pl_fold] def piMinusThree : Exp rT := pl% fun u, &piAffine #3 #1 #()

/-- Bernoulli(numerator/(denominator*pi)), on its valid probability domain. -/
@[pl_fold] def reciprocalPiScaled : Exp rT := pl%
  fun numerator denominator u,
    if (numerator < #0) || (denominator <= #0) then fail else
      &fromBounds (fun n,
        let interval := &piBounds n;
        let lo := (fst(interval));
        let hi := fst(snd(interval));
        let d := snd(snd(interval));
        (numerator * d * lo,
          (numerator * d * hi, denominator * lo * hi))) #()

@[pl_fold] def inversePi : Exp rT := pl% fun u, &reciprocalPiScaled #1 #1 #()

@[pl_fold] def fourOverThreePi : Exp rT := pl% fun u, &reciprocalPiScaled #4 #3 #()

/-- Exact ln(pi)/pi by the geometric reciprocal-pi construction. -/
@[pl_fold] def logPiOverPi : Exp rT := pl%
  fun u,
    let failures := (rec count n := if &inversePi #() then n else count (n + #1));
    let g := failures #0;
    if g = #0 then #false else &Occil.rationalCoin #1 g

@[pl_fold] def inverseSqrtPi : Exp rT := pl%
  fun u, &Occil.fractionalPower &inversePi #1 #2 #()

@[pl_fold] def arctanRationalOverRatio : Exp rT := pl%
  fun x y u, &Occil.arctanOverPFactory (fun v, &Occil.rationalCoin x y) #()

end Occil.Constants
