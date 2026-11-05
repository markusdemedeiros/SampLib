import Samplers.Numerical.Mixtures
import Samplers.Numerical.DistributionFamilies
import Samplers.General.Core
import Samplers.Discrete.Counts
import Samplers.Discrete.Numerical

/-!
Numerical random-stopped distributions and derived unit-valued mixtures.

The stopping counts are ordinary integers; numerical values are Q(scale)
integers. Component draws and the sampled stopping count remain coupled as
specified by the source's extrema and episode constructions.
-/
namespace Occil.Specialized

open ProbLang

variable {rT : Type _}

@[pl_fold] def geometricZeroTruncatedPoisson : Exp rT := pl%
  fun scale poissonRate successProbability u,
    &General.stoppedMaximum
      (fun u, &DiscreteExtra.zeroTruncatedPoisson poissonRate scale)
      (fun u, #1 + &Occil.geometric (fun u, &Numeric.coin scale successProbability #()) #()) #()

@[pl_fold] def exponentialPoisson : Exp rT := pl%
  fun scale exponentialRate poissonRate u,
    &General.stoppedMinimum
      (fun u, &DiscreteExtra.zeroTruncatedPoisson poissonRate scale)
      (fun u, &Numerical.exponential scale exponentialRate #()) #()

@[pl_fold] def poissonExponential : Exp rT := pl%
  fun scale exponentialRate poissonRate u,
    &General.stoppedMaximum
      (fun u, &DiscreteExtra.zeroTruncatedPoisson poissonRate scale)
      (fun u, &Numerical.exponential scale exponentialRate #()) #()

@[pl_fold] def rightTruncatedWeibull : Exp rT := pl%
  fun scale rate shape bound u,
    if (rate <= #0) || (shape <= #0) || (bound <= #0) then fail else
      let poissonRate := &Numeric.mul scale rate (&Numeric.pow scale bound shape);
      &General.stoppedMinimum
        (fun u, &DiscreteExtra.zeroTruncatedPoisson poissonRate scale)
        (fun u, &powerFunction scale shape bound #()) #()

/-- Gamma/geometric episode: return (sum, number of summands). -/
@[pl_fold] def bivariateGammaGeometric : Exp rT := pl%
  fun scale shape rate successProbability u,
    &General.episodes
      (fun u, #1 + &Occil.geometric (fun u, &Numeric.coin scale successProbability #()) #())
      (fun u, &Numerical.gamma scale shape rate #()) #()

@[pl_fold] def bivariateExponentialGeometric : Exp rT := pl%
  fun scale rate successProbability u,
    &bivariateGammaGeometric scale scale rate successProbability #()

@[pl_fold] def unitLindley : Exp rT := pl%
  fun scale theta u,
    let x := &lindley scale theta #();
    &Numeric.div scale x (scale + x)

@[pl_fold] def zeroOneInflatedUnitLindley : Exp rT := pl%
  fun scale mixtureProbability theta zeroProbability u,
    &zeroOneInflated scale mixtureProbability zeroProbability
      (fun u, &unitLindley scale theta #()) #()

@[pl_fold] def grassia : Exp rT := pl%
  fun scale shape rate u,
    &unitDistribution scale (fun u, &Numerical.gamma scale shape rate #()) #false #()

/-- GMDP episode: gamma summands, a discrete-Pareto stopping count. -/
@[pl_fold] def gmdp : Exp rT := pl%
  fun scale shape rate tailShape successProbability u,
    &General.episodes
      (fun u, &DiscreteExtra.discretePareto scale tailShape successProbability #())
      (fun u, &Numerical.gamma scale shape rate #()) #()

end Occil.Specialized
