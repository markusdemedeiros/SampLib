import Samplers.Bernoulli.Powers
import Samplers.Bernoulli.Combinators

/-!
# Linear factories and probability-sensitive arithmetic.

A supplied margin is an assumption on the input probability, not an estimate made by the program.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- Huber's finite gambler's-ruin auxiliary walk. -/
@[pl_fold] def gambler : Exp rT := pl%
  fun coin height a b,
    let loop := (rec walk state :=
      if state = #0 then #true else if height <= state then #false else
        if &Occil.logisticFactory coin a b #() then walk (state - #1)
        else walk (state + #1));
    loop #1

/-- High-power logistic walk, c^m*p^m/(1+cp+...+(cp)^m). -/
@[pl_fold] def highPowerLogistic : Exp rT := pl%
  fun coin height a b,
    let loop := (rec walk state :=
      if state = #0 then #false else if height < state then #true else
        if &Occil.logisticFactory coin a b #() then walk (state + #1)
        else walk (state - #1));
    loop #1

/-- Exact expanding linear factory, (a/b)*p (Huber 2016).
For a>b, assume (a/b)*p <= 1-e/f, with 0<e/f<1. -/
@[pl_fold] def linear : Exp rT := pl%
  rec factory coin a b e f u :=
    if (a < #0) || (b <= #0) then fail else
    if a <= b then
      if &Occil.rationalCoin a b then coin #() else #false
    else if (e <= #0) || (f <= e) then fail else
      let m := (#9 * f + #2 * e - #1) / (#2 * e) + #1;
      let nextA := a * m;
      let nextB := b * (m - #1);
      let nextE := m * e - f;
      let nextF := (m - #1) * f;
      if &gambler coin m nextA nextB then
        if &Occil.rationalCoin (m - #1) m then #true else
          let loop := (rec retry height :=
            if factory coin nextA nextB nextE nextF #() then
              if &highPowerLogistic coin (height - #2) nextA nextB then #true
              else retry (height - #1)
            else #false);
          loop m
      else #false

/-- (c*p)^n, with the same margin condition as `linear`. -/
@[pl_fold] def linearPower : Exp rT := pl%
  fun coin a b n e f u,
    if n < #0 then fail else
      &Occil.iterateCoin (fun u, &linear coin a b e f #()) n

/-- p+q, assuming p+q <= 1-e/f. -/
@[pl_fold] def addition : Exp rT := pl%
  fun p q e f u,
    &linear (fun u, &Occil.coinMean p q #()) #2 #1 e f #()

/-- p-q, assuming p-q >= e/f>0. -/
@[pl_fold] def subtraction : Exp rT := pl%
  fun p q e f u,
    ~(&addition (fun u, ~(p #())) q e f #())

/-- q/p, assuming p-q >= e/f>0. -/
@[pl_fold] def division : Exp rT := pl%
  fun q p e f u,
    &Occil.bernoulliRace q (fun u, &subtraction p q e f #()) #()

/-- eps/p with a known lower bound p>=lower>eps. All bounds are rational. -/
@[pl_fold] def epsilonDivision : Exp rT := pl%
  fun coin a b lowerNum lowerDen u,
    if (a < #0) || (b <= a) || (lowerDen <= #0) || (lowerDen < lowerNum) then fail else
    if a = #0 then #false else
    if lowerNum = lowerDen then &Occil.rationalCoin a b else
      let marginNum := lowerNum * b - a * lowerDen;
      let marginDen := lowerDen * (b - a);
      if marginNum <= #0 then fail else
        let loop := (rec draw u :=
          if &Occil.rationalCoin a b then #true else
            if &linear (fun u, ~(coin #())) b (b - a) marginNum marginDen #()
            then draw #() else #false);
        loop #()

/-- Huber's low-probability linear factory, (a/b)*p <= m/n < 1/2. -/
@[pl_fold] def linearLowProbability : Exp rT := pl%
  fun coin a b m n u,
    if (a < #0) || (b <= #0) || (m < #0) || (n <= #2 * m) then fail else
    if a <= b then
      if &Occil.rationalCoin a b then coin #() else #false
    else if m = #0 then #false else
      let betaDen := n - #2 * m;
      if &Occil.logisticFactory coin (a * n) (b * betaDen) #() then
        if &Occil.rationalCoin betaDen n then #true else
          &linear coin (a * n) (b * #2 * m) (n - m) n #()
      else #false

/-- Huber 2019 joint linear-and-power factory, (c*p)^exponent.
This is the adaptive walk algorithm, distinct from repeated linear-factory calls.
For c=a/b>1 require c*p<=1-e/f, 0<e/f<1. -/
@[pl_fold] def linearPowerWalk : Exp rT := pl%
  fun coin a b exponent e f u,
    if (a < #0) || (b <= #0) || (exponent < #0) then fail else
    if a <= b then
      &Occil.iterateCoin (fun u, if &Occil.rationalCoin a b then coin #() else #false) exponent
    else if (e <= #0) || (f <= e) then fail else
      let loop := (rec draw remaining ca cb marginNum marginDen :=
        if remaining = #0 then #true else
        if #355 * marginDen < #100 * remaining * marginNum then
          let betaNum := #2 * marginDen - marginNum;
          let betaDen := #2 * (marginDen - marginNum);
          if &rationalPower (fun u, &Occil.rationalCoin betaDen betaNum) remaining #1 #()
          then draw remaining (ca * betaNum) (cb * betaDen) marginNum (#2 * marginDen)
          else #false
        else
          let next := (if &Occil.logisticFactory coin ca cb #() then remaining - #1 else remaining + #1);
          draw next ca cb marginNum marginDen);
      loop exponent a b e f

/-- Huber 2014 expanding linear factory. State-space jumps are geometric,
with adaptive probability amplification at the error-dependent threshold. -/
@[pl_fold] def linear2014 : Exp rT := pl%
  fun coin a b e f u,
    if (a < #0) || (b <= #0) then fail else
    if a <= b then
      if &Occil.rationalCoin a b then coin #() else #false
    else if (e <= #0) || (f <= e) then fail else
      let margin := (if #1000 * e <= #644 * f then (e, f) else (#644, #1000));
      let marginNum := fst(margin);
      let marginDen := snd(margin);
      let loop := (rec draw state ca cb en ed thresholdNum thresholdDen :=
        let afterStep := state - #1;
        let next := (if coin #() then afterStep else
          afterStep + #1 + &Occil.geometric (fun u, &Occil.rationalCoin (ca - cb) ca) #());
        if next = #0 then #true else
        if next * thresholdDen < thresholdNum then draw next ca cb en ed thresholdNum thresholdDen
        else
          let factorNum := #2 * ed + en;
          let factorDen := #2 * ed;
          if &rationalPower (fun u, &Occil.rationalCoin factorDen factorNum) next #1 #()
          then draw next (ca * factorNum) (cb * factorDen) en (#2 * ed)
            (#2 * thresholdNum) thresholdDen
          else #false);
      loop #1 a b marginNum marginDen (#23 * marginDen) (#5 * marginNum)

end Occil.FactoryExtra
