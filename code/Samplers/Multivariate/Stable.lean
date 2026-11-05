import Samplers.Multivariate.Linear

/-! Chambers–Mallows–Stuck stable sampling, geometric-stable transformations,
and Best–Fisher circular sampling, following randomnotes.html. Arithmetic and
angles are fixed-point approximations, with radians represented at `scale`. -/
namespace Occil.Multivariate
open ProbLang
variable {rT : Type _}

/-- Standard alpha-stable S1 variate. Alpha is in (0,2], beta in [-1,1]. -/
@[pl_fold] def stable : Exp rT := pl%
  rec draw scale alpha beta u :=
    if (alpha <= #0) || (#2 * scale < alpha) || (scale < &Numeric.abs beta) then fail else
      if alpha = #2 * scale then
        &Numeric.mul scale (&Numeric.sqrt scale (#2 * scale)) (&Numerical.normal scale #0 scale #())
      else
        let halfPi := &Numeric.pi scale / #2;
        let angle := -halfPi + &Numeric.mul scale (#2 * halfPi) (&Numeric.uniform scale #());
        let cosine := &Numeric.cos scale angle;
        let e := &Numerical.exponential scale scale #();
        if (cosine <= #0) || (e <= #0) then draw scale alpha beta #() else
        if alpha = scale then
          let tangent := &Numeric.div scale (&Numeric.sin scale angle) cosine;
          if beta = #0 then tangent else
            let shifted := halfPi + &Numeric.mul scale angle beta;
            let numerator := &Numeric.mul scale halfPi (&Numeric.mul scale e cosine);
            if shifted <= #0 then draw scale alpha beta #() else
              let correction := &Numeric.mul scale beta (&Numeric.log scale (&Numeric.div scale numerator shifted));
              &Numeric.div scale (#2 * (&Numeric.mul scale shifted tangent - correction)) (&Numeric.pi scale)
        else
          let z := -(&Numeric.mul scale (&Numeric.tan scale (&Numeric.mul scale alpha halfPi)) beta);
          let adjusted := angle + &Numeric.div scale (&Numeric.atan scale (-z)) alpha;
          let alphaAngle := &Numeric.mul scale alpha adjusted;
          let inverseAlpha := &Numeric.div scale scale alpha;
          let amplitude := &Numeric.pow scale (scale + &Numeric.mul scale z z) (inverseAlpha / #2);
          let cosinePower := &Numeric.pow scale cosine (-inverseAlpha);
          let base := &Numeric.div scale (&Numeric.cos scale (angle - alphaAngle)) e;
          if base <= #0 then draw scale alpha beta #() else
            let exponent := &Numeric.div scale (scale - alpha) alpha;
            &Numeric.mul scale amplitude
              (&Numeric.mul scale (&Numeric.sin scale alphaAngle)
                (&Numeric.mul scale cosinePower (&Numeric.pow scale base exponent)))

/-- Strictly geometric-stable sampler. |tau|<=min(1,2/alpha-1), lambda>0.
The sign is chosen with probability (1+tau)/2, including negative tau; this
makes explicit the asymmetric sign probability obscured by the article's code. -/
@[pl_fold] def geometricStable : Exp rT := pl%
  fun scale alpha lambda tau u,
    let limit := &Numeric.div scale (#2 * scale) alpha - scale;
    if (alpha <= #0) || (#2 * scale < alpha) || (lambda <= #0) ||
       (scale < &Numeric.abs tau) || (limit < &Numeric.abs tau) then fail else
      let positive := &Occil.rationalCoin (scale + tau) (#2 * scale);
      let rho := (if positive then &Numeric.mul scale alpha (scale + tau) / #2
        else &Numeric.mul scale alpha (scale - tau) / #2);
      let w := (if rho = scale then scale else
        let angle := &Numeric.mul scale rho (&Numeric.pi scale);
        let interior := &Numeric.mul scale angle (&Numeric.uniform scale #());
        &Numeric.div scale (&Numeric.mul scale (&Numeric.sin scale angle) (&Numeric.cos scale interior))
          (&Numeric.sin scale interior) - &Numeric.cos scale angle);
      if w <= #0 then fail else
        let magnitude := &Numeric.mul scale (&Numerical.exponential scale scale #())
          (&Numeric.pow scale (&Numeric.mul scale lambda w) (&Numeric.div scale scale alpha));
        if positive then magnitude else -magnitude

@[pl_fold] def linnik : Exp rT := pl%
  fun scale alpha lambda u, &geometricStable scale alpha lambda #0 #()

@[pl_fold] def mittagLeffler : Exp rT := pl%
  fun scale alpha lambda u,
    if (alpha <= #0) || (scale < alpha) then fail else
      &geometricStable scale alpha lambda scale #()

/-- General geometric-stable law defined by exponential mixing in the S1
parameterization. The alpha=1 logarithmic correction uses 2/pi. -/
@[pl_fold] def generalGeometricStable : Exp rT := pl%
  rec draw scale alpha beta mu sigma u :=
    if sigma <= #0 then fail else
      let z := &Numerical.exponential scale scale #();
      let x := &stable scale alpha beta #();
      let location := &Numeric.mul scale mu z;
      if alpha = scale then
        let stretch := &Numeric.mul scale sigma z;
        if stretch <= #0 then draw scale alpha beta mu sigma #() else
        let correction := &Numeric.div scale
          (#2 * &Numeric.mul scale (&Numeric.mul scale stretch beta) (&Numeric.log scale stretch))
          (&Numeric.pi scale);
        location + &Numeric.mul scale stretch x + correction
      else
        location + &Numeric.mul scale (&Numeric.mul scale sigma x)
          (&Numeric.pow scale z (&Numeric.div scale scale alpha))

/-- Best–Fisher von Mises rejection. The zero-concentration case is uniform.
Concentrations too small to resolve rho use that limiting law; when the
rejection envelope rounds to one, use the wrapped-normal high-kappa approximation. -/
@[pl_fold] def vonMises : Exp rT := pl%
  fun scale mean kappa u,
    if kappa < #0 then fail else
      let pi := &Numeric.pi scale;
      let uniform := (fun u, mean - pi + &Numeric.mul scale (#2 * pi) (&Numeric.uniform scale #()));
      if kappa = #0 then uniform #() else
        let r := scale + &Numeric.sqrt scale (#4 * &Numeric.mul scale kappa kappa + scale);
        let rho := &Numeric.div scale (r - &Numeric.sqrt scale (#2 * r)) (#2 * kappa);
        if rho <= #0 then uniform #() else
          let envelope := &Numeric.div scale (scale + &Numeric.mul scale rho rho) (#2 * rho);
          if envelope <= scale then
            let sigma := &Numeric.sqrt scale (&Numeric.div scale scale kappa);
            if sigma = #0 then mean else
              let centered := &Numerical.normal scale #0 sigma #();
              mean + ((centered + pi) % (#2 * pi)) - pi
          else
          let loop := (rec draw u :=
            let angle := -pi + &Numeric.mul scale (#2 * pi) (&Numeric.uniform scale #());
            let v := &Numeric.uniform scale #();
            let z := &Numeric.cos scale angle;
            let raw := &Numeric.div scale (scale + &Numeric.mul scale envelope z) (envelope + z);
            let w := (if raw < -scale then -scale else if scale < raw then scale else raw);
            let y := &Numeric.mul scale kappa (envelope - w);
            if y <= #0 then draw #() else
              let quick := &Numeric.mul scale y (#2 * scale - y);
              let accept := (if v <= quick then #true else
                #0 <= &Numeric.log scale (&Numeric.div scale y v) + scale - y);
              if accept then
                let residual := scale - &Numeric.mul scale w w;
                let sine := &Numeric.sqrt scale (if residual < #0 then #0 else residual);
                let result := (if w = #0 then pi / #2 else
                  let principal := &Numeric.atan scale (&Numeric.div scale sine w);
                  if w < #0 then principal + pi else principal);
                if angle < #0 then mean - result else mean + result
              else draw #());
          loop #()

end Occil.Multivariate
