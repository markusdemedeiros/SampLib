# Historical source-closure review after the linear-margin repair

Canonical patch author: `/root`. Independent source reviewer: `/root/review_exact_a`.

The [exact implementation-repair review](ExactLowProbabilitySourceRepair001.md)
identifies the single changed declaration and its complete-domain justification.
Its registered exact-byte validation has passed for the current source. This review
covers the **36 historical accepted samplers** whose project-local import closures
include that file; it does not promote the originally defective sampler.

For every entry below I independently recomputed the current source closure and
compared it with its original immutable historical receipt. The set of imported
project-local files is identical. Every proof, support file and other source hash
is identical, except the exact approved one-line replacement in
`code/Samplers/Bernoulli/Linear.lean`. No direct historical sampler declaration is
changed. No other project-local file in these closures even references
`linearLowProbability`, so the repaired declaration is not called or assumed by
these sampler algorithms or their correctness arguments. Their mathematical
laws, parameter domains, encoders and callback interfaces are unchanged.

This is an independent source-change review, not a claim that the historical
reviewer re-reviewed the new dependency. The separate dependency-compatibility
overlay must still rebuild the entire216-entry suite and check all signatures,
standard-only axioms and historical independent callers under the current pin.
The earlier overlay and every historical receipt remain immutable. This receipt
records old and current closure snapshots so the later overlay can validate each
source-change claim exactly.

## Reviewed unchanged direct samplers

- `Occil.FactoryExtra.oneMinusOverOnePlus`
- `Occil.FactoryExtra.onePlusHalf`
- `Occil.FactoryExtra.complementHalf`
- `Occil.FactoryExtra.pLogInverse`
- `Occil.FactoryExtra.oneDivTwoMinus`
- `Occil.FactoryExtra.reciprocalLogistic`
- `Occil.FactoryExtra.complementLogInverse`
- `Occil.FactoryExtra.oddsProduct`
- `Occil.FactoryExtra.polylogarithm`
- `Occil.FactoryExtra.sigmoidDerivative`
- `Occil.FactoryExtra.sigmoidRational`
- `Occil.FactoryExtra.logisticExp`
- `Occil.FactoryExtra.exponentialRatio`
- `Occil.FactoryExtra.tanhRational`
- `Occil.FactoryExtra.reciprocalAffine`
- `Occil.FactoryExtra.reciprocalAffinePower`
- `Occil.FactoryExtra.inverseQuadratic`
- `Occil.FactoryExtra.offsetRace`
- `Occil.FactoryExtra.logOverAffine`
- `Occil.FactoryExtra.reciprocalExpAffine`
- `Occil.FactoryExtra.tanhScaled`
- `Occil.FactoryExtra.sigmoidScaled`
- `Occil.FactoryExtra.exponentialTwist`
- `Occil.FactoryExtra.gambler`
- `Occil.FactoryExtra.highPowerLogistic`
- `Occil.FactoryExtra.linear`
- `Occil.FactoryExtra.complementLogOnePlus`
- `Occil.DiscreteExtra.logarithmicSeries`
- `Occil.FactoryExtra.linearPower`
- `Occil.FactoryExtra.addition`
- `Occil.FactoryExtra.subtraction`
- `Occil.FactoryExtra.division`
- `Occil.FactoryExtra.affine`
- `Occil.FactoryExtra.affineRatio`
- `Occil.FactoryExtra.epsilonDivision`
- `Occil.FactoryExtra.tanhHalfShifted`
