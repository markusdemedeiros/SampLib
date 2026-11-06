# Attic

This directory holds Lean modules that the library no longer builds. `SampLib` imports none
of them, no review covers them, and some of them might not compile.

Each module keeps its old module name, so its imports still show where it used to live.
To revive a module, complete these steps:

1. Move the module back under `SampLib/`, into the directory that the
   [library layout](../SampLib/README.md#layout) assigns to it.
2. Add the module to the build.
3. Build the module through `agent-scripts/lean_gate.py`.

The attic has three parts:

- `SampLib/`: Modules that stopped building before the library was reorganized on
  6 November 2026. The [relocation record](../agent-docs/relocations) lists their old
  paths. Their imports of moved modules use the new names.
- `stopped/`: Unfinished work from the provers that were stopped in round 2.
- `drafts/`: Two early experiments.

## Leftovers for deferred samplers

These files are starting points for the samplers in the
[list of deferred samplers](../agent-docs/ExactCampaignDeferrals.md).

| Sampler | Files |
| --- | --- |
| `newGamma`, `newDirichlet` | `SampLib/PSRNGammaCore`, `SampLib/PSRNGammaIntegerRepresentedCore`, `SampLib/LatentGamma*`, `SampLib/LatentRepresentedGammaInteger`, `SampLib/Syntax/PSRNGamma`, `SampLib/Distributions/GammaErlang`, `stopped/SampLib/Samplers/PSRNGamma`, `stopped/SampLib/Syntax/PSRNGammaSource` |
| `newGaussian`, `newSphere`, `newBall`, `newShell` | `SampLib/LatentNormSquared*`, `SampLib/Syntax/PSRNNormSquared`, `SampLib/Distributions/PSRNSphereLaw` |
| `newBeta` | `SampLib/Distributions/IntegerBetaCDF`, `SampLib/Distributions/PSRNBeta*`, `stopped/SampLib/PSRNJohnkBeta`, `stopped/SampLib/Syntax/PSRNJohnkBeta`, `stopped/SampLib/Distributions/PSRNPowerUniformBeta` |
| `newOrderStatistic`, `newEpanechnikov`, `newArcCosine` | `SampLib/Distributions/UniformOrderStatistic*`, `SampLib/LatentOrderStatistic*`, `stopped/SampLib/Syntax/PSRNOrderStatistic` |
| `newHyperbolicSecant`, `newContinuousBernoulli`, `newCauchy`, `newTulap` | `stopped/SampLib/LatentInlineRejection`, `SampLib/LatentLikelihoodRejection`, `SampLib/LatentPositiveLikelihood`, `SampLib/Distributions/PSRNHyperbolicSecant`, `SampLib/Distributions/AcceptedProposalMap` |
| `newFGMCopula` | `SampLib/Distributions/PSRNFGM` |

Later proofs superseded the other files in `SampLib/`. A few of those files still appear
in the snapshots of superseded receipts or in old review callers. For example, the
`ExactSharedRoot001` receipt lists `LatentRootViews`. No current receipt depends on an
attic file, as `relocation.py --check` and the campaign audit confirm.
