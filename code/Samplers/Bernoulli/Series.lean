import Samplers.Bernoulli.Arithmetic
import Samplers.Continuous
import Samplers.Discrete
import Samplers.Lazy

/-!
# Series, mixtures and adaptive Bernstein-envelope factories.

Adaptive tests retain one shared lazy uniform. Coefficient callbacks must satisfy the stated bounds and consistency conditions.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- An arbitrary rational-coefficient alternating power series. `coeff n`
returns (a_n,b_n), with 0<=a_n/b_n<=1 decreasing to zero. Output probability
is sum_n (-1)^n*(a_n/b_n)*p^n. One cached uniform resolves all partial bounds. -/
@[pl_fold] def alternatingSeries : Exp rT := pl%
  fun coin coeff u,
    let bag := &Occil.newUniformBag #();
    let initial := coeff #0;
    let loop := (rec draw n lower upper weight :=
      let nextWeight := (if weight then coin #() else #false);
      let c := (if nextWeight then coeff n else (#0, #1));
      let lo := (if n % #2 = #1 then &subtractFraction upper c else lower);
      let hi := (if n % #2 = #0 then &addFraction lower c else upper);
      if &Occil.uniformBagLess bag (fst(lo)) (snd(lo)) then #true else
        if &Occil.uniformBagLess bag (fst(hi)) (snd(hi)) then
          draw (n + #1) lo hi nextWeight
        else #false);
    loop #1 (#0, #1) initial #true

/-- Finite nonnegative power series, normalized by the integer coefficient sum. -/
@[pl_fold] def positivePowerSeries : Exp rT := pl%
  fun coin coefficients u,
    let degree := &Occil.weightedChoice coefficients;
    &Occil.iterateCoin coin degree

/-- Mendo power-series factory: 1-sum_i c_i*(1-p)^(i+1), normalized integer c_i. -/
@[pl_fold] def complementPowerSeries : Exp rT := pl%
  fun coin coefficients u,
    let degree := &Occil.weightedChoice coefficients + #1;
    ~(&Occil.iterateCoin (fun u, ~(coin #())) degree)

/-- Infinite nonnegative coefficient scheme: `hazard n` returns
c_n/(1-sum_{i<n}c_i) as a rational pair, with sum c_i=1.
Output 1-sum_n c_n*(1-p)^(n+1). -/
@[pl_fold] def powerSeriesHazards : Exp rT := pl%
  fun coin hazard u,
    let loop := (rec draw n :=
      if coin #() then #true else
        let h := hazard n;
        if &Occil.rationalCoin (fst(h)) (snd(h)) then #false else draw (n + #1));
    loop #0

/-- A finite mixture of coin callbacks, with nonnegative integer weights. -/
@[pl_fold] def convexCombination : Exp rT := pl%
  fun weights coins u,
    let i := &Occil.weightedChoice weights;
    let selected := &Occil.getAt coins i;
    selected #()

/-- An integral mixture: sample X from the supplied law, then run a coin whose
conditional probability is f(X). The parameter sampler and factory are callbacks. -/
@[pl_fold] def integralMixture : Exp rT := pl%
  fun parameter factory u,
    let x := parameter #();
    factory x #()

/-- General reverse-time Bernstein-envelope factory with caller-selected degrees.
`bounds n heads` returns (lower,upper), each a rational pair; `nextDegree n` must
strictly increase and `nextDegree 0` must be positive. Coefficients must lie in
[0,1], satisfy degree-elevation consistency, and converge to the same function.
Old coefficients are averaged under the exact conditional hypergeometric law;
the unresolved uniform interval is rescaled as in Occil's general algorithm.
Arbitrary confidence intervals are not admissible coefficient envelopes. -/
@[pl_fold] def envelopeFactoryDegrees : Exp rT := pl%
  fun coin bounds nextDegree u,
    let bag := &Occil.newUniformBag #();
    let loop := (rec draw previousDegree oldHeads lowerThreshold upperThreshold :=
      let degree := nextDegree previousDegree;
      if degree <= previousDegree then fail else
        let heads := oldHeads + &Occil.binomial coin (degree - previousDegree);
        let current := bounds degree heads;
        let lower := fst(current);
        let upper := snd(current);
        let conditional := (fun high,
          if previousDegree = #0 then if high then (#1, #1) else (#0, #1) else
            let denominator := &choose degree heads;
            let average := (rec sum j total :=
              if previousDegree < j then total else
                let weight := &choose previousDegree j *
                  &choose (degree - previousDegree) (heads - j);
                if weight = #0 then sum (j + #1) total else
                  let previous := bounds previousDegree j;
                  let coefficient := (if high then snd(previous) else fst(previous));
                  let term := &multiplyFraction coefficient (weight, denominator);
                  sum (j + #1) (&addFraction total term));
            average #0 (#0, #1));
        let oldLower := conditional #false;
        let oldUpper := conditional #true;
        let remaining := &subtractFraction upperThreshold lowerThreshold;
        let oldWidth := &subtractFraction oldUpper oldLower;
        let factor := &divideFraction remaining oldWidth;
        let lowerGap := &subtractFraction lower oldLower;
        let upperGap := &subtractFraction oldUpper upper;
        let nextLower := &addFraction lowerThreshold (&multiplyFraction lowerGap factor);
        let nextUpper := &subtractFraction upperThreshold (&multiplyFraction upperGap factor);
        if &Occil.uniformBagLess bag (fst(nextLower)) (snd(nextLower)) then #true else
          if &Occil.uniformBagLess bag (fst(nextUpper)) (snd(nextUpper)) then
            draw degree heads nextLower nextUpper
          else #false);
    loop #0 #0 (#0, #1) (#1, #1)

/-- Consecutive-degree specialization of the general envelope algorithm. -/
@[pl_fold] def envelopeFactory : Exp rT := pl%
  fun coin bounds u, &envelopeFactoryDegrees coin bounds (fun n, n + #1) #()

/-- A numerical plug-in factory. With N fresh trials, its exact probability is
E[f(scale*Binomial(N,p)/N)/scale], not generally f(p). This is an explicitly
approximate factory, converging for bounded continuous f as N and scale increase.
`evaluate scale estimatedP` is a deterministic fixed-point numerical callback. -/
@[pl_fold] def approximateFactory : Exp rT := pl%
  fun coin trials scale evaluate u,
    if (trials <= #0) || (scale <= #0) then fail else
      let heads := &Occil.binomial coin trials;
      let value := evaluate scale (scale * heads / trials);
      let probability := (if value < #0 then #0 else if scale < value then scale else value);
      &Occil.rationalCoin probability scale

/-- min(p,1-p), via Occil's Catalan-mixture Bernstein construction. The initial
fair walk can have infinite expected length, although it terminates a.s. -/
@[pl_fold] def minimumComplement : Exp rT := pl%
  fun coin u,
    let walk := (rec draw state steps :=
      if state < #0 then (steps + #1) / #2 else
        if &Occil.fairCoin #() then draw (state + #1) (steps + #1)
        else draw (state - #1) (steps + #1));
    let m := walk #0 #0;
    let r := (#2 * m) / #3 + #1;
    let d := #2 * m + r;
    let heads := &Occil.binomial coin d;
    if (heads < m) || (m + r < heads) then #false else
      let numerator := &intPower #4 m * &choose r (heads - m);
      let denominator := #2 * &choose d heads;
      &Occil.rationalCoin numerator denominator

@[pl_fold] def minimumHalf : Exp rT := pl%
  fun coin u,
    if &Occil.fairCoin #() then coin #() else &minimumComplement coin #()

end Occil.FactoryExtra
