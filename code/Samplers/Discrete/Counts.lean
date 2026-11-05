import Samplers.Discrete.Combinatorics
import Samplers.Discrete

/-!
# Count distributions and rational mixtures

Rational parameters are passed as separate integer numerator and denominator arguments.
Geometric and negative-binomial counts mean failures before the required successes.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Negative binomial with a positive rational shape, by rejection from its
ceiling-shape integer negative binomial (Occil's `PolyaInt`). -/
@[pl_fold] def polyaRational : Exp rT := pl%
  fun shapeNumerator shapeDenominator successNumerator successDenominator,
    if (shapeNumerator <= #0) || (shapeDenominator <= #0) ||
       (successNumerator <= #0) || (successDenominator < successNumerator)
    then fail else
      let ceiling := (shapeNumerator + shapeDenominator - #1) / shapeDenominator;
      let loop := (rec draw u :=
        let value := &Occil.negativeBinomial
          (fun u, &Occil.rationalCoin successNumerator successDenominator) ceiling;
        let products := (rec build i top bottom :=
          if i = value then (top, bottom) else
            build (i + #1) (top * (shapeNumerator + i * shapeDenominator))
              (bottom * ((ceiling + i) * shapeDenominator)));
        let ratio := products #0 #1 #1;
        if &Occil.rationalCoin (fst(ratio)) (snd(ratio)) then value else draw #());
      loop #()

/-- Failures before a prescribed number of successes in a reinforced urn. -/
@[pl_fold] def inversePolya : Exp rT := pl%
  rec draw successes ones zeros reinforcement :=
    if (successes < #0) || (ones <= #0) || (zeros < #0) || (reinforcement < #0)
    then fail else if successes = #0 then #0 else
      if &Occil.rationalCoin ones (ones + zeros) then
        draw (successes - #1) (ones + reinforcement) zeros reinforcement
      else #1 + draw successes ones (zeros + reinforcement) reinforcement

/-- Beta-negative-binomial mixture with positive rational beta shapes. -/
@[pl_fold] def betaNegativeBinomial : Exp rT := pl%
  fun successes alphaNumerator alphaDenominator betaNumerator betaDenominator,
    if (alphaNumerator <= #0) || (alphaDenominator <= #0) ||
       (betaNumerator <= #0) || (betaDenominator <= #0)
    then fail else
      &inversePolya successes (alphaNumerator * betaDenominator)
        (betaNumerator * alphaDenominator) (alphaDenominator * betaDenominator)

/-- Waring–Yule: one success in a beta-mixed geometric distribution. -/
@[pl_fold] def waringYule : Exp rT := pl%
  fun alphaNumerator alphaDenominator betaNumerator betaDenominator,
    &betaNegativeBinomial #1 alphaNumerator alphaDenominator betaNumerator betaDenominator

/-- Yule–Simon(rho), supported on positive integers; rho is a positive rational. -/
@[pl_fold] def yuleSimon : Exp rT := pl%
  fun numerator denominator,
    #1 + &betaNegativeBinomial #1 numerator denominator #1 #1

/-- Borel(lambda): total progeny of a Poisson branching process.
Requires 0 <= lambda < 1. -/
@[pl_fold] def borel : Exp rT := pl%
  fun numerator denominator,
    if (numerator < #0) || (denominator <= numerator) then fail else
      let loop := (rec go pending population :=
        if pending = #0 then population else
          let offspring := &Occil.poissonRational numerator denominator;
          go (pending - #1 + offspring) (population + #1));
      loop #1 #0

/-- Logarithmic-series(p), 0 < p < 1, by geometric proposals and 1/n rejection. -/
@[pl_fold] def logarithmicSeries : Exp rT := pl%
  fun numerator denominator,
    if (numerator <= #0) || (denominator <= numerator) then fail else
      let loop := (rec draw u :=
        let n := #1 + &Occil.geometric
          (fun u, &Occil.rationalCoin (denominator - numerator) denominator) #();
        if &Occil.rationalCoin #1 n then n else draw #());
      loop #()

/-- Poisson conditioned to be strictly positive. -/
@[pl_fold] def zeroTruncatedPoisson : Exp rT := pl%
  rec draw numerator denominator :=
    if (numerator <= #0) || (denominator <= #0) then fail else
      let n := &Occil.poissonRational numerator denominator;
      if n = #0 then draw numerator denominator else n

end Occil.DiscreteExtra
