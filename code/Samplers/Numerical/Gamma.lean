import Samplers.Numerical.Normal

/-!
General gamma and beta algorithms, including small-shape rejection.

Real parameters and results use signed Q(scale) integers; scale is explicit.
These are numerical implementations, not certified exact-real samplers.
Unless stated otherwise, a final unit argument requests a fresh draw.
-/
namespace Occil.Numerical

open ProbLang

variable {rT : Type _}

/-- Gamma(shape,rate), using the Marsaglia–Tsang construction in `GammaDist`.
For shape below one, augment the shape and apply the power-of-uniform correction. -/
@[pl_fold] def gamma : Exp rT := pl%
  fun scale shape rate u,
    if (shape <= #0) || (rate <= #0) then fail else
    if shape = scale then &exponential scale rate #() else
      let adjusted := (if shape < scale then shape + scale else shape);
      let d := adjusted - scale / #3;
      let c := &Numeric.div scale scale (&Numeric.sqrt scale (#9 * d));
      let loop := (rec draw u :=
        let x := &normal scale #0 scale #();
        let base := scale + &Numeric.mul scale c x;
        if base <= #0 then draw #() else
          let v := &Numeric.mul scale base (&Numeric.mul scale base base);
          if v <= #0 then draw #() else
            let uniform := &Numeric.uniform scale #();
            let x2 := &Numeric.mul scale x x;
            let squeeze := scale - #331 * &Numeric.mul scale x2 x2 / #10000;
            let bound := x2 / #2 + &Numeric.mul scale d (scale - v + &Numeric.log scale v);
            if (uniform < squeeze) || (&Numeric.log scale uniform < bound) then
              &Numeric.mul scale d v
            else draw #());
      let result := loop #();
      let corrected := (if shape < scale then
        &Numeric.mul scale result (&Numeric.pow scale (&Numeric.uniform scale #())
          (&Numeric.div scale scale shape)) else result);
      &positiveGrid (&Numeric.div scale corrected rate)

/-- General beta via the two-gamma ratio, including direct unit-shape transforms. -/
@[pl_fold] def beta : Exp rT := pl%
  rec draw scale a b u :=
    if (a <= #0) || (b <= #0) then fail else
    if (a = scale) && (b = scale) then &Numeric.uniform scale #() else
    if a = scale then scale - &Numeric.pow scale (&Numeric.uniform scale #())
      (&Numeric.div scale scale b) else
    if (b = scale) && (a < #10 * scale) then
      &Numeric.pow scale (&Numeric.uniform scale #()) (&Numeric.div scale scale a)
    else
      let x := &gamma scale a scale #();
      let y := &gamma scale b scale #();
      if x + y <= #0 then draw scale a b #() else &Numeric.div scale x (x + y)

/-- Liu–Martin–Syring small-shape gamma rejection, recommended for shape<0.3.
The more general `gamma` entry point uses shape augmentation instead. -/
@[pl_fold] def gammaSmallShape : Exp rT := pl%
  rec draw scale shape rate u :=
    if (shape <= #0) || (scale <= shape) || (rate <= #0) then fail else
      let lambda := &Numeric.div scale scale shape - scale;
      let weight := &Numeric.mul scale
        (&Numeric.div scale shape (scale - shape)) (&Numeric.exp scale scale);
      let split := &Numeric.div scale scale (scale + weight);
      let x := &Numeric.uniform scale #();
      let z := (if x <= split then -(&Numeric.log scale (&Numeric.div scale x split))
        else -(&exponential scale lambda #()));
      let result := &Numeric.exp scale (-(&Numeric.div scale z shape));
      let envelope := (if #0 <= z then &Numeric.exp scale (-z) else
        &Numeric.mul scale (&Numeric.mul scale weight lambda)
          (&Numeric.exp scale (&Numeric.mul scale lambda z)));
      let target := &Numeric.exp scale (-result - z);
      if &Numeric.mul scale (&Numeric.uniform scale #()) envelope < target then
        &positiveGrid (&Numeric.div scale result rate)
      else draw scale shape rate #()

end Occil.Numerical
