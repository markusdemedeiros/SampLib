import Samplers.Numerical.Core

/-!
Normal algorithms, approximations, and normal-based transformations.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

/-- Box–Muller: two independent numerical normal variates. -/
@[pl_fold] def normalBoxMuller : Exp rT := pl%
  fun scale mean sigma u,
    if sigma <= #0 then fail else
      let radius := &Numeric.sqrt scale (-#2 * &Numeric.log scale (&Numeric.uniform scale #()));
      let angle := #2 * &Numeric.mul scale (&Numeric.pi scale) (&Numeric.uniform scale #());
      let x := &Numeric.mul scale radius (&Numeric.cos scale angle);
      let y := &Numeric.mul scale radius (&Numeric.sin scale angle);
      (mean + &Numeric.mul scale sigma x, mean + &Numeric.mul scale sigma y)

/-- Marsaglia polar rejection, as `NormalPolar` in the companion article. -/
@[pl_fold] def normalPolar : Exp rT := pl%
  rec draw scale mean sigma u :=
    if sigma <= #0 then fail else
      let a := #2 * &Numeric.uniform scale #() - scale;
      let b := #2 * &Numeric.uniform scale #() - scale;
      let radius2 := &Numeric.mul scale a a + &Numeric.mul scale b b;
      if (radius2 <= #0) || (scale <= radius2) then draw scale mean sigma #() else
        let factor := &Numeric.sqrt scale
          (&Numeric.div scale (-#2 * &Numeric.log scale radius2) radius2);
        (mean + &Numeric.mul scale sigma (&Numeric.mul scale a factor),
         mean + &Numeric.mul scale sigma (&Numeric.mul scale b factor))

/-- Scalar normal, using one coordinate of the polar construction. -/
@[pl_fold] def normal : Exp rT := pl%
  fun scale mean sigma u, fst(&normalPolar scale mean sigma #())

/-- Ratio-of-uniforms rejection with Occil's rational envelope 858/1000. -/
@[pl_fold] def normalRatioOfUniforms : Exp rT := pl%
  rec draw scale mean sigma u :=
    if sigma <= #0 then fail else
      let a := &Numeric.uniform scale #();
      let b := #858 * &Numeric.uniform scale #() / #1000;
      let a2 := &Numeric.mul scale a a;
      if &Numeric.mul scale b b <= -#4 * &Numeric.mul scale a2 (&Numeric.log scale a) then
        let z := &Numeric.div scale b a;
        let signed := (if &Occil.fairCoin #() then z else -z);
        mean + &Numeric.mul scale sigma signed
      else draw scale mean sigma #()

/-- Normal by numerical inversion; distinct from the rejection algorithms above. -/
@[pl_fold] def normalInversion : Exp rT := pl%
  fun scale mean sigma u,
    if sigma <= #0 then fail else
      mean + &Numeric.mul scale sigma
        (&Numeric.normalQuantile scale (&Numeric.uniform scale #()))

/-- The explicitly approximate twelve-uniform central-limit construction. -/
@[pl_fold] def normalCLT : Exp rT := pl%
  fun scale mean sigma u,
    if sigma <= #0 then fail else
      let sum := (rec add remaining total :=
        if remaining = #0 then total else
          add (remaining - #1) (total + &Numeric.uniform scale #()));
      mean + &Numeric.mul scale sigma (sum #12 #0 - #6 * scale)

@[pl_fold] def lognormal : Exp rT := pl%
  fun scale mean sigma u, &Numeric.exp scale (&normal scale mean sigma #())

/-- Michael–Schucany–Haas inverse Gaussian, mean and shape strictly positive. -/
@[pl_fold] def inverseGaussian : Exp rT := pl%
  fun scale mean shape u,
    if (mean <= #0) || (shape <= #0) then fail else
      let z := &normal scale #0 scale #();
      let y := &Numeric.mul scale z z;
      let my := &Numeric.mul scale mean y;
      let t := &Numeric.div scale my (#2 * shape);
      let root := &Numeric.sqrt scale
        (&Numeric.mul scale t (#2 * scale + t));
      let candidate := &positiveGrid (&Numeric.div scale mean (scale + t + root));
      if candidate <= #0 then fail else
        if &Numeric.coin scale (&Numeric.div scale mean (mean + candidate)) #() then candidate
        else &positiveGrid (&Numeric.div scale (&Numeric.mul scale mean mean) candidate)

@[pl_fold] def halfNormal : Exp rT := pl%
  fun scale sigma u, &Numeric.abs (&normal scale #0 sigma #())

@[pl_fold] def birnbaumSaunders : Exp rT := pl%
  fun scale shape rate u,
    if rate <= #0 then fail else
      let x := &normal scale #0 shape #();
      let y := &Numeric.sqrt scale (#4 * scale + &Numeric.mul scale x x) + x;
      &Numeric.div scale (&Numeric.mul scale y y) (#4 * rate)

/-- Azzalini skew-normal construction from two independent standard normals. -/
@[pl_fold] def skewNormal : Exp rT := pl%
  fun scale shape location width u,
    if width <= #0 then fail else
      let delta := &Numeric.div scale shape
        (&Numeric.sqrt scale (scale + &Numeric.mul scale shape shape));
      let a := &Numeric.abs (&normal scale #0 scale #());
      let b := &normal scale #0 scale #();
      let z := &Numeric.mul scale delta a + &Numeric.mul scale
        (&Numeric.sqrt scale (scale - &Numeric.mul scale delta delta)) b;
      location + &Numeric.mul scale width z

/-- The selection construction for generalized skew-normal SNE(lambda,xi). -/
@[pl_fold] def generalizedSkewNormal : Exp rT := pl%
  rec draw scale shape offset u :=
    let y := &normal scale #0 scale #();
    let z := &normal scale #0 scale #();
    if z < &Numeric.mul scale y shape + offset then y else draw scale shape offset #()

/-- Moyal from -log(Z^2), Z standard normal. -/
@[pl_fold] def moyal : Exp rT := pl%
  rec draw scale location width u :=
    if width <= #0 then fail else
      let z := &normal scale #0 scale #();
      let z2 := &Numeric.mul scale z z;
      if z2 <= #0 then draw scale location width #() else
        location - &Numeric.mul scale width (&Numeric.log scale z2)

@[pl_fold] def powerNormal : Exp rT := pl%
  fun scale shape location width u,
    if (shape <= #0) || (width <= #0) then fail else
      let p := scale - &Numeric.pow scale (&Numeric.uniform scale #())
        (&Numeric.div scale scale shape);
      let probability := (if p <= #0 then #1 else if scale <= p then scale - #1 else p);
      location + &Numeric.mul scale width (&Numeric.normalQuantile scale probability)

@[pl_fold] def powerLognormal : Exp rT := pl%
  fun scale shape location width u,
    &Numeric.exp scale (&powerNormal scale shape location width #())

/-- Kabal's polynomial correction to the explicitly approximate twelve-uniform normal. -/
@[pl_fold] def normalCLTWarped : Exp rT := pl%
  fun scale mean sigma u,
    let x := &normalCLT scale #0 scale #();
    let square := &Numeric.mul scale x x;
    let polynomial := #9874600000 + &Numeric.mul scale square
      (#39439000 + &Numeric.mul scale square
        (#747400 + &Numeric.mul scale square (-#5102 + &Numeric.mul scale square #1141)));
    if sigma <= #0 then fail else
      mean + &Numeric.mul scale sigma (x * polynomial / #10000000000)

/-- General centered/normalized k-uniform CLT approximation. -/
@[pl_fold] def normalCLTK : Exp rT := pl%
  fun scale count u,
    if count <= #0 then fail else
      let loop := (rec sum remaining total := if remaining = #0 then total else
        sum (remaining - #1) (total + &Numeric.uniform scale #() - scale / #2));
      &Numeric.div scale (loop count #0) (&Numeric.sqrt scale (count * scale / #12))

/-- Generalized Box–Muller q-Gaussian pair, q<3. For q=1 this is the normal pair;
otherwise the returned coordinates share a radius and are not independent. -/
@[pl_fold] def qGaussian : Exp rT := pl%
  fun scale q mean width u,
    if (#3 * scale <= q) || (width <= #0) then fail else
      let transformed := &Numeric.div scale (scale + q) (#3 * scale - q);
      let power := scale - transformed;
      let x := &Numeric.uniform scale #();
      let radius2 := (if power = #0 then -#2 * &Numeric.log scale x else
        -#2 * &Numeric.div scale (&Numeric.pow scale x power - scale) power);
      let radius := &Numeric.sqrt scale radius2;
      let angle := #2 * &Numeric.mul scale (&Numeric.pi scale) (&Numeric.uniform scale #());
      (mean + &Numeric.mul scale width (&Numeric.mul scale radius (&Numeric.cos scale angle)),
       mean + &Numeric.mul scale width (&Numeric.mul scale radius (&Numeric.sin scale angle)))

/-- Conditional-normal SNE(lambda,xi) construction, distinct from selection rejection.
The index omits the factor il on the independent Z coordinate; this restores the
variance-preserving coefficient implied by the named distribution. -/
@[pl_fold] def generalizedSkewNormalConditional : Exp rT := pl%
  fun scale shape offset u,
    let inverseLength := &Numeric.div scale scale
      (&Numeric.sqrt scale (scale + &Numeric.mul scale shape shape));
    let delta := &Numeric.mul scale shape inverseLength;
    let lower := -(&Numeric.mul scale offset inverseLength);
    let truncated := (rec draw u :=
      let y := &normal scale #0 scale #();
      if lower < y then y else draw #());
    if shape = #0 then &normal scale #0 scale #() else
      &Numeric.mul scale delta (truncated #()) +
      &Numeric.mul scale inverseLength (&normal scale #0 scale #())

/-- Source max/min skew-normal construction, with its mixing coefficient supplied
explicitly: c*max(A,B)+(1-c)*min(A,B), A,B independent standard normals.
Unlike the index's contradictory theta special-case text, this parameterization
is unambiguous. The internal distribution's scale depends on c; c=1/2 gives
N(0,1/2), and c=1 or0 gives the maximum or minimum of two normals. -/
@[pl_fold] def skewNormalExtremes : Exp rT := pl%
  fun scale coefficient location width u,
    if (width <= #0) || (coefficient < #0) || (scale < coefficient) then fail else
      let a := &normal scale #0 scale #();
      let b := &normal scale #0 scale #();
      let low := (if a < b then a else b);
      let high := (if a < b then b else a);
      let z := &Numeric.mul scale coefficient high +
        &Numeric.mul scale (scale - coefficient) low;
      location + &Numeric.mul scale width z

end Occil.Numerical
