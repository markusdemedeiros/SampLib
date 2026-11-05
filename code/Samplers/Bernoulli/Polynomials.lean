import Samplers.Bernoulli.Series
import Samplers.Bernoulli.Combinators

/-!
# Polynomial, rational-polynomial and piecewise-linear factories.

Power-basis coefficients are rational pairs; conversion and degree elevation execute inside ProbLang.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- Polynomial evaluation through automatic Bernstein degree elevation.
Power-basis coefficients are rational pairs. This exact algorithm terminates
once all elevated Bernstein coefficients lie in [0,1]; for example, strict
0<f(p)<1 on the whole closed unit interval guarantees eventual admissibility. -/
@[pl_fold] def polynomial : Exp rT := pl%
  fun coin coefficients u,
    let degree := &Occil.length coefficients - #1;
    if degree < #0 then fail else
      let convert := (rec elevate n :=
        let coefficient := (fun k,
          let sum := (rec terms j value :=
            if (degree < j) || (k < j) then value else
              let a := &Occil.getAt coefficients j;
              let numerator := &choose k j;
              let denominator := &choose n j;
              let term := &multiplyFraction a (numerator, denominator);
              terms (j + #1) (&addFraction value term));
          sum #0 (#0, #1));
        let all := (rec collect k :=
          if n < k then inl(#()) else inr((coefficient k, collect (k + #1))));
        let bernstein := all #0;
        let valid := (rec check xs := case! xs
          | inl(v) => #true
          | inr(pair) =>
            let value := fst(pair);
            if ((fst(value)) < #0) || ((snd(value)) < (fst(value))) then #false
            else check (snd(pair)));
        if valid bernstein then &Occil.bernsteinFactory coin bernstein #()
        else elevate (n + #1));
      convert degree

/-- A(p)/(A(p)+B(p)) with polynomial numerator/complement denominator.
Each supplied polynomial must itself be an admissible probability polynomial. -/
@[pl_fold] def rationalFunction : Exp rT := pl%
  fun coin numerator complementDenominator u,
    &Occil.bernoulliRace (fun u, &polynomial coin numerator #())
      (fun u, &polynomial coin complementDenominator #()) #()

/-- Piecewise-linear source constructions with breakpoints at 0,1/2,1.
mode 0: (0,nu/2,nu*mu); 1: ((1-mu)/2,1/2,mu/2);
2: (0,mu/2,mu/2); 3: (mu,1/2,0); 4: (1,1/2,mu);
5: (mu,1/2,1). -/
@[pl_fold] def threePointPiecewise : Exp rT := pl%
  fun coin mu nu mode u,
    if mode = #0 then
      if nu #() then
        if mu #() then coin #() else &minimumComplement coin #()
      else #false
    else if mode = #1 then
      if &Occil.fairCoin #() then &minimumComplement coin #() else
        if mu #() then coin #() else ~(coin #())
    else if mode = #2 then
      if mu #() then &minimumHalf coin #() else #false
    else if mode = #3 then
      if mu #() then ~(coin #()) else &minimumComplement coin #()
    else if mode = #4 then
      if mu #() then ~(&minimumComplement coin #()) else ~(coin #())
    else if mode = #5 then
      if mu #() then ~(&minimumComplement coin #()) else coin #()
    else fail

end Occil.FactoryExtra
