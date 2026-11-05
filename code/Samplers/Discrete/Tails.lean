import Samplers.Discrete.Combinatorics
import Samplers.Discrete
import Samplers.Continuous

/-!
# Geometric and power-law tails

Exact integer and rational constructions for symmetric geometric, discrete Laplace,
log-uniform, Zipf, zeta, and continuation-defined laws.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Extend the power factory to any nonnegative rational exponent. -/
@[pl_fold] def rationalPowerCoin : Exp rT := pl%
  fun coin numerator denominator u,
    if (numerator < #0) || (denominator <= #0) then fail else
      if &Occil.iterateCoin coin (numerator / denominator) then
        let remainder := numerator % denominator;
        if remainder = #0 then #true else
          &Occil.fractionalPower coin remainder denominator #()
      else #false

/-- Symmetric geometric with tails proportional to (1-p)^|k|.
The input coin has success probability p>0. -/
@[pl_fold] def symmetricGeometric : Exp rT := pl%
  fun coin u,
    let n := &Occil.geometric coin #();
    if &Occil.oneDivOnePlus (fun u, ~(coin #())) #() then n else -#1 - n

/-- Canonne et al. exact discrete Laplace with rational epsilon=s/t>0. -/
@[pl_fold] def discreteLaplace : Exp rT := pl%
  fun numerator denominator,
    if (numerator <= #0) || (denominator <= #0) then fail else
      let loop := (rec draw u :=
        let remainder := &Occil.uniformInt denominator;
        if &Occil.expMinusRational remainder denominator #() then
          let whole := &Occil.geometricFailures
            (fun u, &Occil.expMinusRational #1 #1 #()) #0;
          let magnitude := (remainder + whole * denominator) / numerator;
          if &Occil.fairCoin #() then magnitude else
            if magnitude = #0 then draw #() else -magnitude
        else draw #());
      loop #()

/-- Abseil-style log-uniform integers in [0,maximum], integer base>=2. -/
@[pl_fold] def logUniform : Exp rT := pl%
  fun maximum base,
    if (maximum < #0) || (base < #2) then fail else
      let ceilingLog := (rec count power exponent :=
        if maximum + #1 <= power then exponent else count (power * base) (exponent + #1));
      let level := &Occil.rndInt (ceilingLog #1 #0);
      if level = #0 then #0 else
        let lowerPower := &integerPower base (level - #1);
        let upperPower := &integerPower base level - #1;
        let lower := (if maximum < lowerPower then maximum else lowerPower);
        let upper := (if maximum < upperPower then maximum else upperPower);
        &Occil.rndIntRange lower upper

/-- Zipf on 1..bound, with any nonnegative rational exponent. Uniform proposals
are accepted with probability candidate^(-exponent), using exact power factories. -/
@[pl_fold] def zipf : Exp rT := pl%
  fun bound exponentNumerator exponentDenominator,
    if (bound <= #0) || (exponentNumerator < #0) || (exponentDenominator <= #0)
    then fail else
      let loop := (rec draw u :=
        let value := #1 + &Occil.uniformInt bound;
        if &rationalPowerCoin (fun u, &Occil.rationalCoin #1 value)
            exponentNumerator exponentDenominator #() then value else draw #());
      loop #()

/-- Zeta(alpha), alpha>1 rational. Dyadic blocks form an exact geometric
proposal; within-block acceptance is (blockStart/value)^alpha. -/
@[pl_fold] def zeta : Exp rT := pl%
  fun exponentNumerator exponentDenominator,
    if (exponentDenominator <= #0) || (exponentNumerator <= exponentDenominator)
    then fail else
      let proposalCoin := (fun u,
        ~(&rationalPowerCoin (fun u, &Occil.fairCoin #())
          (exponentNumerator - exponentDenominator) exponentDenominator #()));
      let loop := (rec draw u :=
        let level := &Occil.geometric proposalCoin #();
        let start := &integerPower #2 level;
        let value := start + &Occil.uniformInt start;
        if &rationalPowerCoin (fun u, &Occil.rationalCoin start value)
            exponentNumerator exponentDenominator #() then value else draw #());
      loop #()

/-- Generalized geometric: rho(k) returns a continuation coin at positive k. -/
@[pl_fold] def generalizedGeometric : Exp rT := pl%
  fun continuation,
    let loop := (rec draw k := if continuation k then draw (k + #1) else k);
    loop #1

/-- Generalized Sibuya with alpha>0, nu>=0 and alpha<nu+1, all rational. -/
@[pl_fold] def generalizedSibuya : Exp rT := pl%
  fun alphaNumerator alphaDenominator nuNumerator nuDenominator,
    if (alphaNumerator <= #0) || (alphaDenominator <= #0) ||
       (nuNumerator < #0) || (nuDenominator <= #0) ||
       (alphaDenominator * (nuNumerator + nuDenominator) <= alphaNumerator * nuDenominator)
    then fail else
      let loop := (rec draw k :=
        if &Occil.rationalCoin (alphaNumerator * nuDenominator)
            (alphaDenominator * (nuNumerator + k * nuDenominator)) then k
        else draw (k + #1));
      loop #1

/-- Himanshu: failures before n consecutive coin successes in independent blocks. -/
@[pl_fold] def himanshu : Exp rT := pl%
  fun coin blockSize,
    if blockSize <= #0 then fail else
      &Occil.geometric (fun u, &Occil.iterateCoin coin blockSize) #()

end Occil.DiscreteExtra
