import Samplers.PSRN.BetaGamma
import Samplers.Discrete

/-!
# Derived scalar and dependent lazy samplers

Rejection and mixture constructions preserve accepted lazy values and
their shared latent randomness. Distribution-specific domains are documented
on the individual constructors.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

@[pl_fold] def newRayleigh : Exp rT := pl%
  fun u,
    let e := &newExponential #1 #1 #();
    &root (&scaleRational e #2 #1) #2

/-- Exact Cauchy by rejection inside the unit disk and a coordinate ratio. -/
@[pl_fold] def newCauchy : Exp rT := pl%
  fun u,
    let draw := (rec retry u :=
      let x := &subtract (&scaleRational (&newUniform #()) #2 #1) (&rational #1 #1);
      let y := &subtract (&scaleRational (&newUniform #()) #2 #1) (&rational #1 #1);
      let radius := &add (&multiply x x) (&multiply y y);
      if &less radius (&rational #1 #1) then &divide y x else retry #());
    draw #()

/-- Continuous Bernoulli(lambda) for rational lambda in (0,1). Uses a truncated
exponential at rate abs(log(lambda/(1-lambda))), with reflection above 1/2. -/
@[pl_fold] def newContinuousBernoulli : Exp rT := pl%
  fun numerator denominator u,
    if (numerator <= #0) || (denominator <= numerator) then fail else
      if #2 * numerator = denominator then &newUniform #() else
        let ratioNumerator := (if #2 * numerator < denominator then denominator - numerator else numerator);
        let ratioDenominator := (if #2 * numerator < denominator then numerator else denominator - numerator);
        let draw := (rec retry u :=
          let x := &newExponentialLogRate ratioNumerator ratioDenominator #();
          if &less x (&rational #1 #1) then x else retry #());
        let x := draw #();
        if #2 * numerator < denominator then x else &subtract (&rational #1 #1) x

/-- Epanechnikov kernel on [-1,1]: twice the median of three uniforms minus one. -/
@[pl_fold] def newEpanechnikov : Exp rT := pl%
  fun u,
    let median := &newOrderStatistic #3 #2;
    &subtract (&scaleRational median #2 #1) (&rational #1 #1)

/-- Farlie–Gumbel–Morgenstern copula by rejection under envelope two.
Returns two dependent oracle values; theta is a rational in [-1,1]. -/
@[pl_fold] def newFGMCopula : Exp rT := pl%
  fun numerator denominator u,
    if (denominator <= #0) || (numerator < -denominator) || (denominator < numerator) then fail else
      let draw := (rec retry u :=
        let x := &newUniform #();
        let y := &newUniform #();
        let one := &rational #1 #1;
        let a := &subtract one (&scaleRational x #2 #1);
        let b := &subtract one (&scaleRational y #2 #1);
        let density := &add one (&scaleRational (&multiply a b) numerator denominator);
        let threshold := &scaleRational (&newUniform #()) #2 #1;
        if &less threshold density then (x, y) else retry #());
      draw #()

/-- Hyperbolic-secant law in its natural scale, density sech(x)/pi.
An independent sign is applied after exponential-envelope rejection. -/
@[pl_fold] def newHyperbolicSecant : Exp rT := pl%
  fun u,
    let draw := (rec retry u :=
      let x := &newExponential #1 #1 #();
      let coin := (fun u, &expMinusCoin (&scaleRational x #2 #1) #());
      if &oneDivOnePlus coin #() then x else retry #());
    let x := draw #();
    if &fairCoin #() then x else &negate x

/-- Arc-cosine distribution on [0,1], CDF 1-cos(pi*x/2), using Occil's
alternating maximum-of-uniforms algorithm and exact pi/4 coin trials. -/
@[pl_fold] def newArcCosine : Exp rT := pl%
  fun u,
    let draw := (rec retry u :=
      let candidate := &newOrderStatistic #2 #2;
      let loop := (rec trial m :=
        let other := &newOrderStatistic #2 #2;
        let proceed := (if &less other candidate then
          if &rationalCoin #4 (#4 * m * m + #2 * m) then
            if &arctanFactory (fun u, #true) #() then
              &arctanFactory (fun u, #true) #()
            else #false
          else #false
        else #false);
        if proceed then trial (m + #1) else m);
      let parity := loop #1;
      if parity % #2 = #1 then candidate else retry #());
    draw #()

/-- Tulap(b,q): difference of geometric failure counts plus centered uniform,
then retain the middle 1-q quantile mass. b and q are exact rational parameters.
At q=0 this is the untruncated Tulap distribution. -/
@[pl_fold] def newTulap : Exp rT := pl%
  fun bn bd qn qd u,
    if (bn <= #0) || (bd <= bn) || (qn < #0) || (qd <= qn) then fail else
      let draw := (rec retry u :=
        let success := (fun u, &rationalCoin (bd - bn) bd);
        let k := &geometric success #() - &geometric success #();
        let fraction := &newUniform #();
        let x := &add (&rational (#2 * k - #1) #2) fraction;
        if qn = #0 then x else
          let magnitude := (if k < #0 then -k else k);
          let pn := &integerPower bn magnitude;
          let pd := &integerPower bd magnitude;
          let denominator := (bn + bd) * pd;
          let base := (if k <= #0 then bn * pn else denominator - bd * pn);
          let cdf := &add (&rational base denominator)
            (&scaleRational fraction ((bd - bn) * pn) denominator);
          if &less (&rational qn (#2 * qd)) cdf then
            if &less cdf (&rational (#2 * qd - qn) (#2 * qd)) then x else retry #()
          else retry #());
      draw #()

/-- Named Lindley-family specializations from the PSRN article's mixture table. -/
@[pl_fold] def newGarima : Exp rT := pl%
  fun n d u, &newGammaMixture (n + d) (n + #2 * d) #1 #2 n d #()

@[pl_fold] def newIGarima : Exp rT := pl%
  fun n d u, &newGammaMixture (n + #2 * d) (n + #3 * d) #1 #2 n d #()

@[pl_fold] def newWeightedExponentialGamma : Exp rT := pl%
  fun n d u, &newGammaMixture n (n + d) #2 #3 n d #()

@[pl_fold] def newXgamma : Exp rT := pl%
  fun n d u, &newGammaMixture n (n + d) #1 #3 n d #()

@[pl_fold] def newMirra : Exp rT := pl%
  fun n d an ad u,
    if (an <= #0) || (ad <= #0) then fail else
      &newGammaMixture (n * n * ad) (an * d * d + n * n * ad) #1 #3 n d #()

@[pl_fold] def newSushila : Exp rT := pl%
  fun n d scaleNumerator scaleDenominator u,
    if (scaleNumerator <= #0) || (scaleDenominator <= #0) then fail else
      &scaleRational (&newLindley n d #()) scaleNumerator scaleDenominator

@[pl_fold] def newXLindley : Exp rT := pl%
  fun n d u,
    if &rationalCoin n (n + d) then &newExponential n d #() else &newLindley n d #()

/-- Uniform quarter/full rectellipse, integer radii and rational squareness in
[0,1]. The acceptance polynomial is the one in Occil's rectellipse section. -/
@[pl_fold] def newRectellipse : Exp rT := pl%
  fun radiusX radiusY sn sd full u,
    if (radiusX <= #0) || (radiusY <= #0) || (sn < #0) || (sd <= #0) || (sd < sn) then fail else
      let draw := (rec retry u :=
        let x := &newUniform #();
        let y := &newUniform #();
        let xx := &multiply x x;
        let yy := &multiply y y;
        let limit := &add (&rational #1 #1)
          (&scaleRational (&multiply xx yy) (sn * sn) (sd * sd));
        if &less (&add xx yy) limit then (x, y) else retry #());
      let point := draw #();
      let x := &scaleRational (fst(point)) radiusX #1;
      let y := &scaleRational (snd(point)) radiusY #1;
      if full then
        let xx := (if &fairCoin #() then x else &negate x);
        let yy := (if &fairCoin #() then y else &negate y);
        (xx, yy)
      else (x, y)

end Occil.PSRN
