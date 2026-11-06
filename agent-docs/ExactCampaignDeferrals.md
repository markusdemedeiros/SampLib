# Deferred exact-campaign samplers

Round 2 closed on 6 November 2026 with 120 of 137 entries accepted. The other 17 entries
stay `in_progress` in the ledger and are deferred. None of them has an accepted proof.
Accept one only after a fresh proof and an independent review against
[the standard](VerifyingSamplers.md).

| Sampler | Reason | Notes |
| --- | --- | --- |
| `Occil.PSRN.newGamma` | Proof stopped unfinished | The fractional-shape branch is incomplete. |
| `Occil.PSRN.newGaussian` | Proof stopped unfinished | Blocks `newSphere`, `newBall`, and `newShell`. |
| `Occil.PSRN.newNormal` | Proof stopped unfinished | Wraps `newGaussian`. |
| `Occil.PSRN.newBeta` | Proof stopped unfinished | Uses the Jöhnk method. Reuse the accepted `newPowerUniform`. |
| `Occil.PSRN.newSphere` | Needs a `newGaussian` spec | See the [geometry notes](progress/ExactPSRNGeometryProgress.md). |
| `Occil.PSRN.newBall` | Needs `newSphere` | Can reuse `newPowerUniform` with a = 1 and b = n. |
| `Occil.PSRN.newShell` | Needs `newSphere` | Also needs admissibility for the root of an affine uniform. |
| `Occil.PSRN.newDirichlet` | Needs a `newGamma` spec | The support for simplex normalization carries over. |
| `Occil.PSRN.newOrderStatistic` | Proof stopped unfinished | Needs an insertion-sort invariant on the joint uniform world. |
| `Occil.PSRN.newEpanechnikov` | Needs `newOrderStatistic` | See the [distribution notes](progress/ExactPSRNDistributionsProgress.md). |
| `Occil.PSRN.newArcCosine` | Needs `newOrderStatistic` | Also needs a conditional arctangent coin. |
| `Occil.PSRN.newHyperbolicSecant` | Inline rejection loop unproved | Needs `expMinusCoin` admissibility for 2x. |
| `Occil.PSRN.newContinuousBernoulli` | Inline rejection loop unproved | Needs the left subtraction `1 - x`. |
| `Occil.PSRN.newCauchy` | Inline rejection loop unproved | Needs a comparison with a shared operand, and x ≠ 0 almost surely. |
| `Occil.PSRN.newTulap` | Inline rejection loop unproved | No supporting proofs exist yet. |
| `Occil.PSRN.newFGMCopula` | Rejected: no spec kind fits | Returns a pair, but `latent_vector` needs a list. |
| `Occil.PSRN.newRectellipse` | Rejected: no spec kind fits | Same as `newFGMCopula`. See the [vector notes](progress/ExactPSRNVectorRejectionProgress.md). |

The two samplers that return pairs need a protocol decision first. Either add a pair spec
kind, or generalize the vector spec over its output encoding. Either choice also needs an
extension to the auditor.

The unfinished files from the stopped provers are in [`attic/stopped`](../attic/stopped).
Older support for these samplers, which no longer builds, is in
[`attic/SampLib`](../attic/SampLib). The [attic notes](../attic/README.md) match each file
to its sampler. The stopped gamma work edited `attic/SampLib/PSRNGammaCore.lean`, and no
one reviewed that edit.
