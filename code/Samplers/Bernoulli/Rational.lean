import Samplers.Bernoulli.Linear

/-!
# Affine, reciprocal and rational callback-coin constructions.

Each input coin is unit-taking. Domain and margin assumptions are stated at the relevant term.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- d/(c+p), with c=a/b, d=x/y, 0<=d<=c, c>0. -/
@[pl_fold] def reciprocalAffine : Exp rT := pl%
  rec draw coin a b x y u :=
    if (a <= #0) || (b <= #0) || (x < #0) || (y <= #0) then fail else
      let c := a * y;
      let d := x * b;
      let denominatorScale := b * y;
      if c < d then fail else
        let choice := &Occil.uniformInt (c + denominatorScale);
        if choice < d then #true else if choice < c then #false else
          if coin #() then #false else draw coin a b x y #()

/-- (d+p)/c with rational d,c and an explicit margin when expansion is needed. -/
@[pl_fold] def affine : Exp rT := pl%
  fun coin a b x y e f u,
    if (a <= #0) || (b <= #0) || (x < #0) || (y <= #0) then fail else
      let mixed := (fun u, if &Occil.rationalCoin x (x + y) then #true else coin #());
      &linear mixed ((x + y) * b) (y * a) e f #()

/-- (d+q)/(c+p). For c>=d+1, use direct disjoint-event rejection without
a margin; otherwise assume the normalized denominator exceeds numerator by e/f.
K=(a*y+b*x+b*y)/(b*y) bounds both offsets plus one. -/
@[pl_fold] def affineRatio : Exp rT := pl%
  fun p q a b x y e f u,
    if (a < #0) || (b <= #0) || (x < #0) || (y <= #0) then fail else
      let denominatorScale := b * y;
      let c := a * y;
      let d := x * b;
      let k := c + d + denominatorScale;
      let denominator := (fun u,
        let choice := &Occil.uniformInt k;
        if choice < c then #true else if choice < c + denominatorScale then p #() else #false);
      let numerator := (fun u,
        let choice := &Occil.uniformInt k;
        if choice < d then #true else if choice < d + denominatorScale then q #() else #false);
      if d + denominatorScale <= c then
        let loop := (rec draw u :=
          let choice := &Occil.uniformInt (c + denominatorScale);
          if choice < d then #true else
          if choice < d + denominatorScale then q #() else
          if choice < c then #false else
            if p #() then #false else draw #());
        loop #()
      else &division numerator denominator e f #()

/-- Reciprocal logistic: 1/(1+(a/b)*p), a>=0,b>0. -/
@[pl_fold] def reciprocalLogistic : Exp rT := pl%
  fun coin a b u,
    if a = #0 then #true else ~(&Occil.logisticFactory coin a b #())

@[pl_fold] def oneDivTwoMinus : Exp rT := pl%
  fun coin u, &Occil.oneDivOnePlus (fun u, ~(coin #())) #()

/-- 1/(1+(m+p)^2), integer m>=0. -/
@[pl_fold] def inverseQuadratic : Exp rT := pl%
  fun coin m u,
    if m < #0 then fail else
      let mixed := (fun u,
        if &Occil.rationalCoin (#2 * m) (#2 * m + #1) then coin #()
        else &Occil.iterateCoin coin #2);
      &reciprocalAffine mixed (m * m + #1) (#2 * m + #1) #1 (#2 * m + #1) #()

/-- (d/(c+p))^k, with c=a/b,d=x/y. -/
@[pl_fold] def reciprocalAffinePower : Exp rT := pl%
  fun coin a b x y k u,
    if k < #0 then fail else
      &Occil.iterateCoin (fun u, &reciprocalAffine coin a b x y #()) k

/-- (d+q)/(c+p+d+q), with nonnegative rational offsets c=a/b,d=x/y. -/
@[pl_fold] def offsetRace : Exp rT := pl%
  fun p q a b x y u,
    if (a < #0) || (b <= #0) || (x < #0) || (y <= #0) then fail else
      let denominatorScale := b * y;
      let c := a * y;
      let d := x * b;
      let total := c + d + denominatorScale;
      let left := (fun u,
        let choice := &Occil.uniformInt total;
        if choice < d then #true else if choice < d + denominatorScale then q #() else #false);
      let right := (fun u,
        let choice := &Occil.uniformInt total;
        if choice < c then #true else if choice < c + denominatorScale then p #() else #false);
      &Occil.bernoulliRace left right #()

/-- 1/(c+exp(-z)), c=a/b>=1,z=x/y>=0. -/
@[pl_fold] def reciprocalExpAffine : Exp rT := pl%
  fun a b x y u,
    &reciprocalAffine (fun u, &Occil.expMinusRational x y #()) a b #1 #1 #()

/-- mu*p/(1-mu+mu*p), requiring mu<1 or p>0. -/
@[pl_fold] def oddsProduct : Exp rT := pl%
  rec draw coin mu u :=
    if mu #() then if coin #() then #true else draw coin mu #() else #false

end Occil.FactoryExtra
