# Attic

Lean modules that the library no longer builds. Nothing here is reviewed or imported by
`SampLib`, and some files may not compile. Each keeps its old module name, so its own
imports still say where it used to live. To revive one, move it back under `SampLib/`,
give it a place in the [layout](../SampLib/README.md#layout), add it to the build and
build it through `agent-scripts/lean_gate.py`.

- `SampLib/`: unbuilt modules from before the [2026-11-06 move](../agent-docs/relocations).
  The move recorded their paths, and imports of modules that were moved were rewritten.
- `stopped/`: unfinished work from provers that were stopped in round 2.
- `drafts/`: two early probes.

## Leftovers for deferred samplers

These are starting points for the samplers in
[the deferral list](../agent-docs/ExactCampaignDeferrals.md).

| Target | Files |
| --- | --- |
| `newGamma`, `newDirichlet` | `SampLib/PSRNGammaCore`, `SampLib/PSRNGammaIntegerRepresentedCore`, `SampLib/LatentGamma*`, `SampLib/LatentRepresentedGammaInteger`, `SampLib/Syntax/PSRNGamma`, `SampLib/Distributions/GammaErlang`, `stopped/SampLib/Samplers/PSRNGamma`, `stopped/SampLib/Syntax/PSRNGammaSource` |
| `newGaussian`, `newSphere`, `newBall`, `newShell` | `SampLib/LatentNormSquared*`, `SampLib/Syntax/PSRNNormSquared`, `SampLib/Distributions/PSRNSphereLaw` |
| `newBeta` | `SampLib/Distributions/IntegerBetaCDF`, `SampLib/Distributions/PSRNBeta*`, `stopped/SampLib/PSRNJohnkBeta`, `stopped/SampLib/Syntax/PSRNJohnkBeta`, `stopped/SampLib/Distributions/PSRNPowerUniformBeta` |
| `newOrderStatistic`, `newEpanechnikov`, `newArcCosine` | `SampLib/Distributions/UniformOrderStatistic*`, `SampLib/LatentOrderStatistic*`, `stopped/SampLib/Syntax/PSRNOrderStatistic` |
| `newHyperbolicSecant`, `newContinuousBernoulli`, `newCauchy`, `newTulap` | `stopped/SampLib/LatentInlineRejection`, `SampLib/LatentLikelihoodRejection`, `SampLib/LatentPositiveLikelihood`, `SampLib/Distributions/PSRNHyperbolicSecant`, `SampLib/Distributions/AcceptedProposalMap` |
| `newFGMCopula` | `SampLib/Distributions/PSRNFGM` |

The other `SampLib/` files were superseded. A few still appear in the snapshots of
superseded receipts (`LatentRootViews` in `ExactSharedRoot001`, for example) or in old
review callers. Current receipts depend on none of them; `relocation.py --check` and the
campaign audit confirm this.
