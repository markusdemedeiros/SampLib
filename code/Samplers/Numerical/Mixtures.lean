import Samplers.Numerical
import Samplers.Discrete

/-!
Numerical mixtures, skew constructions, and tilted distributions.

All numerical arguments and results are Q(scale) integers. Integer counts are
identified in individual comments. These finite-grid terms do not claim the
exact PSRN laws of their sources. Existing public names remain in
`Occil.Specialized` for compatibility.
-/
namespace Occil.Specialized

open ProbLang

variable {rT : Type _}

/-- Numerical Erlang mixture. `a` and `b` are positive integer shape counts. -/
@[pl_fold] def erlangMixture : Exp rT := pl%
  fun scale weight rate a b u,
    if (a <= #0) || (b <= #0) then fail else
      let shape := (if &Numeric.coin scale weight #() then a else b);
      &Numerical.gamma scale (shape * scale) rate #()

@[pl_fold] def lindley : Exp rT := pl%
  fun scale theta u,
    &erlangMixture scale (&Numeric.div scale theta (scale + theta)) theta #1 #2 #()

@[pl_fold] def garima : Exp rT := pl%
  fun scale theta u,
    &erlangMixture scale (&Numeric.div scale (scale + theta) (#2 * scale + theta))
      theta #1 #2 #()

@[pl_fold] def iGarima : Exp rT := pl%
  fun scale theta u,
    &erlangMixture scale (&Numeric.div scale (#2 * scale + theta) (#3 * scale + theta))
      theta #1 #2 #()

@[pl_fold] def weightedExponentialGamma : Exp rT := pl%
  fun scale theta u,
    &erlangMixture scale (&Numeric.div scale theta (scale + theta)) theta #2 #3 #()

@[pl_fold] def xgamma : Exp rT := pl%
  fun scale theta u,
    &erlangMixture scale (&Numeric.div scale theta (scale + theta)) theta #1 #3 #()

@[pl_fold] def mirra : Exp rT := pl%
  fun scale alpha theta u,
    if alpha <= #0 then fail else
      let squared := &Numeric.mul scale theta theta;
      &erlangMixture scale (&Numeric.div scale squared (alpha + squared)) theta #1 #3 #()

@[pl_fold] def sushila : Exp rT := pl%
  fun scale alpha theta u,
    if alpha <= #0 then fail else &Numeric.mul scale alpha (&lindley scale theta #())

@[pl_fold] def xLindley : Exp rT := pl%
  fun scale theta u,
    if &Numeric.coin scale (&Numeric.div scale theta (scale + theta)) #() then
      &Numerical.exponential scale theta #()
    else &lindley scale theta #()

@[pl_fold] def gammaExponential : Exp rT := pl%
  fun scale delta t nu r shape u,
    if (delta <= #0) || (nu = #0) || (r < #0) || (scale <= r) then fail else
      let numerator := &Numeric.pow scale (&Numerical.gamma scale t scale #())
        (&Numeric.div scale scale nu);
      let denominator := &Numeric.pow scale (&Numerical.gamma scale shape scale #())
        (&Numeric.div scale r nu);
      &Numeric.mul scale delta (&Numeric.div scale numerator denominator)

@[pl_fold] def extendedXgamma : Exp rT := pl%
  fun scale theta alpha beta u,
    if (theta <= #0) || (alpha <= #0) || (beta < #0) then fail else
      let extra := (if &Numeric.coin scale (&Numeric.div scale theta (theta + beta)) #()
        then #0 else #2 * scale);
      &Numerical.gamma scale (alpha + extra) theta #()

/-- Generic skew-symmetric construction; both callbacks return numerical values. -/
@[pl_fold] def skewSymmetric : Exp rT := pl%
  fun scale symmetricSampler thresholdSampler oddFunction u,
    let z := symmetricSampler #();
    if thresholdSampler #() <= oddFunction z then z else -z

@[pl_fold] def logarithmicSkewNormal : Exp rT := pl%
  fun scale shape location width u,
    if width <= #0 then fail else
      &Numeric.exp scale (location + &Numeric.mul scale width
        (&Numerical.generalizedSkewNormal scale shape shape #()))

/-- Two-piece family, from an arbitrary symmetric numerical sampler. -/
@[pl_fold] def twoPiece : Exp rT := pl%
  fun scale location leftWidth rightWidth symmetricSampler u,
    if (leftWidth <= #0) || (rightWidth <= #0) then fail else
      let magnitude := &Numeric.abs (symmetricSampler #());
      if &Numeric.coin scale (&Numeric.div scale leftWidth (leftWidth + rightWidth)) #()
      then location - &Numeric.mul scale magnitude leftWidth
      else location + &Numeric.mul scale magnitude rightWidth

@[pl_fold] def asymmetricGeneralizedGaussian : Exp rT := pl%
  fun scale shape location leftWidth rightWidth u,
    &twoPiece scale location leftWidth rightWidth
      (fun u, &Numerical.generalizedNormal scale shape #0 scale #()) #()

@[pl_fold] def offsetSymmetricGaussian : Exp rT := pl%
  fun scale offset width u,
    if (offset <= #0) || (width <= #0) then fail else
      let loop := (rec draw u :=
        let y := &Numerical.normal scale #0 width #();
        if y < offset then draw #() else y - offset);
      let magnitude := loop #();
      if &Occil.fairCoin #() then magnitude else -magnitude

@[pl_fold] def tiltedBeta : Exp rT := pl%
  fun scale mixtureProbability tilt a b u,
    if &Numeric.coin scale mixtureProbability #() then &Numerical.beta scale a b #() else
      let loop := (rec draw u :=
        let x := &Numeric.uniform scale #();
        let first := &Numeric.coin scale x #();
        let second := &Numeric.coin scale tilt #();
        if first = second then x else draw #());
      loop #()

/-- n is an ordinary integer count, the other parameters are fixed point. -/
@[pl_fold] def tiltedBetaBinomial : Exp rT := pl%
  fun scale n mixtureProbability tilt a b u,
    let p := &tiltedBeta scale mixtureProbability tilt a b #();
    &Occil.binomial (fun u, &Numeric.coin scale p #()) n

/-- Suzuki mixture: a Rayleigh variate whose scale is independently lognormal.
The numerical grid can round a lognormal scale to zero; redraw before calling
the positive-scale Rayleigh routine. -/
@[pl_fold] def suzuki : Exp rT := pl%
  rec draw scale logMean logSigma u :=
    let width := &Numerical.lognormal scale logMean logSigma #();
    if width <= #0 then draw scale logMean logSigma #() else
      &Numerical.rayleigh scale width #()

end Occil.Specialized
