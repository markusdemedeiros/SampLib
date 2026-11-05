import Samplers.Numerical.Gamma
import Samplers.Discrete

/-!
Mixture samplers and rejection from piecewise or bounded densities.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

/-- Hypoexponential: sum of independent exponentials with the supplied positive rates. -/
@[pl_fold] def hypoexponential : Exp rT := pl%
  rec draw scale rates u := case! rates | inl(v) => #0 | inr(p) =>
    &exponential scale (fst(p)) #() + draw scale (snd(p)) #()

/-- Hyperexponential: integer mixture weights and fixed-point component rates. -/
@[pl_fold] def hyperexponential : Exp rT := pl%
  fun scale rates weights u,
    if &Occil.length rates = &Occil.length weights then
      let index := &Occil.weightedChoice weights;
      &exponential scale (&Occil.getAt rates index) #()
    else fail

/-- Piecewise-linear density through increasing knots and nonnegative heights.
Area weighting chooses the segment; each segment is a rectangle/triangle mixture. -/
@[pl_fold] def piecewiseLinear : Exp rT := pl%
  fun scale points heights u,
    let count := &Occil.length points;
    if (count < #2) || (~(&Occil.length heights = count)) then fail else
      let areas := (rec build index :=
        if index + #1 = count then inl(#()) else
          let lo := &Occil.getAt points index;
          let hi := &Occil.getAt points (index + #1);
          let a := &Occil.getAt heights index;
          let b := &Occil.getAt heights (index + #1);
          if (hi <= lo) || (a < #0) || (b < #0) then fail else
            inr(((hi - lo) * (a + b), build (index + #1))));
      let index := &Occil.weightedChoice (areas #0);
      let lo := &Occil.getAt points index;
      let hi := &Occil.getAt points (index + #1);
      let a := &Occil.getAt heights index;
      let b := &Occil.getAt heights (index + #1);
      let difference := &Numeric.abs (b - a);
      let x := &Numeric.uniform scale #();
      let fraction := (if &Occil.rationalCoin difference (a + b) then
        if a <= b then &Numeric.sqrt scale x else scale - &Numeric.sqrt scale x
        else x);
      lo + &Numeric.mul scale (hi - lo) fraction

/-- Piecewise-constant density on intervals between increasing knots. -/
@[pl_fold] def piecewiseConstant : Exp rT := pl%
  fun scale points heights u,
    let count := &Occil.length heights;
    if (count <= #0) || (~(&Occil.length points = count + #1)) then fail else
      let areas := (rec build index :=
        if index = count then inl(#()) else
          let lo := &Occil.getAt points index;
          let hi := &Occil.getAt points (index + #1);
          let height := &Occil.getAt heights index;
          if (hi <= lo) || (height < #0) then fail else
            inr(((hi - lo) * height, build (index + #1))));
      let index := &Occil.weightedChoice (areas #0);
      &uniformRange scale (&Occil.getAt points index) (&Occil.getAt points (index + #1)) #()

/-- Sine-power density on [0,pi], using the beta-envelope rejection in the index. -/
@[pl_fold] def sinePower : Exp rT := pl%
  rec draw scale power u :=
    if power <= #0 then fail else
      let pi := &Numeric.pi scale;
      let x := &Numeric.mul scale pi (&beta scale (power + scale) (power + scale) #());
      if (x <= #0) || (pi <= x) then draw scale power #() else
        let denominator := #4 * &Numeric.mul scale x (pi - x);
        let numerator := &Numeric.mul scale (&Numeric.mul scale pi pi) (&Numeric.sin scale x);
        let ratio := &Numeric.div scale numerator denominator;
        if ratio <= #0 then draw scale power #() else
          if -(&exponential scale power #()) <= &Numeric.log scale ratio then x
          else draw scale power #()

end Occil.Numerical
