import Samplers.Numerical.SpecialDistributions

/-!
Quantile-defined and reweighted numerical distribution families.

A component quantile consumes one Q(scale) probability and returns one value.
Callbacks are the source construction's component samplers, CDFs, and quantiles;
they are not oracles for the resulting target distribution.
-/
namespace Occil.Specialized

open ProbLang

variable {rT : Type _}

@[pl_fold] def xG : Exp rT := pl%
  fun scale componentSampler quantile u, quantile (componentSampler #())

@[pl_fold] def expG : Exp rT := pl%
  fun scale rate quantile u,
    let x := &Numeric.uniform scale #();
    if rate = #0 then quantile x else
      let c := &Numeric.exp scale (-rate) - scale;
      let transformed := -(&Numeric.div scale
        (&Numeric.log scale (scale + &Numeric.mul scale c x)) rate);
      quantile transformed

@[pl_fold] def alphaPowerTransformed : Exp rT := pl%
  fun scale alpha quantile u,
    if alpha <= #0 then fail else &expG scale (-(&Numeric.log scale alpha)) quantile #()

@[pl_fold] def exponentiatedG : Exp rT := pl%
  fun scale shape quantile u,
    if shape <= #0 then fail else
      quantile (&Numeric.pow scale (&Numeric.uniform scale #()) (&Numeric.div scale scale shape))

@[pl_fold] def transmutedG : Exp rT := pl%
  fun scale eta quantile u,
    if scale < &Numeric.abs eta then fail else
      let x := &Numeric.uniform scale #();
      if &Numeric.coin scale (scale - &Numeric.abs eta) #() then quantile x else
        let y := &Numeric.uniform scale #();
        let maximum := (if x < y then y else x);
        quantile (if eta < #0 then scale - maximum else maximum)

@[pl_fold] def cubicRankTransmuted : Exp rT := pl%
  fun scale firstWeight secondWeight quantile u,
    if (firstWeight < #0) || (scale < firstWeight) ||
      (secondWeight < #0) || (scale < secondWeight) then fail else
      let x := &Numeric.uniform scale #();
      let y := &Numeric.uniform scale #();
      let z := &Numeric.uniform scale #();
      let xyMin := (if x < y then x else y);
      let xyMax := (if x < y then y else x);
      let minimum := (if xyMin < z then xyMin else z);
      let maximum := (if xyMax < z then z else xyMax);
      let middle := x + y + z - minimum - maximum;
      let category := &Occil.weightedChoice
        (inr((firstWeight, inr((secondWeight,
          inr((#3 * scale - firstWeight - secondWeight, inl(#()))))))));
      quantile (if category = #0 then minimum else if category = #1 then middle else maximum)

@[pl_fold] def biweightG : Exp rT := pl%
  rec draw scale quantile u :=
    let x := &Numeric.uniform scale #();
    let complement := scale - &Numeric.mul scale x x;
    if &Numeric.coin scale (&Numeric.mul scale complement complement) #()
    then quantile x else draw scale quantile #()

@[pl_fold] def transformedTransformer : Exp rT := pl%
  fun scale componentSampler inverseTransform quantile u,
    quantile (inverseTransform (componentSampler #()))

@[pl_fold] def tRY : Exp rT := pl%
  fun scale componentSampler componentCDF quantile u,
    quantile (componentCDF (componentSampler #()))

@[pl_fold] def oddXG : Exp rT := pl%
  fun scale componentSampler quantile u,
    let x := componentSampler #();
    quantile (&Numeric.div scale x (scale + x))

@[pl_fold] def oddLogLogisticG : Exp rT := pl%
  fun scale shape quantile u,
    if shape <= #0 then fail else
      let x := &Numeric.pow scale (&uniformOdds scale #()) (&Numeric.div scale scale shape);
      quantile (&Numeric.div scale x (scale + x))

@[pl_fold] def rayleighG : Exp rT := pl%
  fun scale width quantile u,
    quantile (&Numeric.exp scale (-(&Numerical.rayleigh scale width #())))

@[pl_fold] def rayleighRayleigh : Exp rT := pl%
  fun scale componentWidth targetWidth u,
    let quantile := (fun probability,
      &Numeric.mul scale targetWidth
        (&Numeric.sqrt scale (-#2 * &Numeric.log scale (scale - probability))));
    &rayleighG scale componentWidth quantile #()

@[pl_fold] def generalizedGammaG : Exp rT := pl%
  fun scale shape power width quantile u,
    let x := &Numerical.generalizedGamma scale shape power #0 width #();
    quantile (&Numeric.exp scale (-x))

@[pl_fold] def inverseDistribution : Exp rT := pl%
  fun scale sampler u, &Numeric.div scale scale (sampler #())

/-- Rejection weighting; `weight x` must be a probability in [0,scale].
Unbounded nonnegative weighting requires a separate proposal/envelope. -/
@[pl_fold] def weightedDistribution : Exp rT := pl%
  rec draw scale sampler weight u :=
    let x := sampler #();
    if &Numeric.coin scale (weight x) #() then x else draw scale sampler weight #()

@[pl_fold] def inflatedDistribution : Exp rT := pl%
  fun scale atom probability sampler u,
    if &Numeric.coin scale probability #() then atom else sampler #()

@[pl_fold] def zeroOneInflated : Exp rT := pl%
  fun scale atomProbability zeroProbability sampler u,
    if &Numeric.coin scale atomProbability #() then
      if &Numeric.coin scale zeroProbability #() then #0 else scale
    else sampler #()

@[pl_fold] def unitDistribution : Exp rT := pl%
  fun scale sampler complementary u,
    let x := &Numeric.exp scale (-(sampler #()));
    if complementary then scale - x else x

/-- Smithson–Shou CDF–quantile family. Flags identify positive support. -/
@[pl_fold] def cdfQuantileFamily : Exp rT := pl%
  fun scale sampler cdf inputPositive outputPositive location width u,
    if width <= #0 then fail else
      let x := sampler #();
      let transformed := (if inputPositive then &Numeric.log scale x else x);
      let z := location + &Numeric.mul scale width transformed;
      cdf (if outputPositive then &Numeric.exp scale z else z)

end Occil.Specialized
