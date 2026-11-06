# Deferred exact-campaign samplers (2026-11-06)

Round 2 closed at 120 of 137 accepted. The remaining 17 entries stay `in_progress` in the
ledger and are deferred. None has an accepted proof, and none should be accepted without a
fresh proof and independent review against [the standard](VerifyingSamplers.md).

| Sampler | Reason deferred | Notes |
| --- | --- | --- |
| `Occil.PSRN.newGamma` | Proof stopped unfinished | Fractional-shape branch incomplete |
| `Occil.PSRN.newGaussian` | Proof stopped unfinished | Blocks sphere, ball, shell |
| `Occil.PSRN.newNormal` | Proof stopped unfinished | Wraps newGaussian |
| `Occil.PSRN.newBeta` | Proof stopped unfinished | Jöhnk route; reuse accepted newPowerUniform |
| `Occil.PSRN.newSphere` | Needs a newGaussian spec | [Geometry notes](ExactPSRNGeometryProgress.md) |
| `Occil.PSRN.newBall` | Needs newSphere | Can reuse newPowerUniform (a=1, b=n) |
| `Occil.PSRN.newShell` | Needs newSphere | Also needs root-of-affine-uniform admissibility |
| `Occil.PSRN.newDirichlet` | Needs a newGamma spec | Simplex normalization support carries over |
| `Occil.PSRN.newOrderStatistic` | Proof stopped unfinished | Insertion-sort invariant on the joint uniform world |
| `Occil.PSRN.newEpanechnikov` | Needs newOrderStatistic | [Distribution notes](ExactPSRNDistributionsProgress.md) |
| `Occil.PSRN.newArcCosine` | Needs newOrderStatistic | Also a conditional arctan coin |
| `Occil.PSRN.newHyperbolicSecant` | Inline rejection loop unproved | `expMinusCoin` admissibility for 2x |
| `Occil.PSRN.newContinuousBernoulli` | Inline rejection loop unproved | Needs left subtraction `1 - x` |
| `Occil.PSRN.newCauchy` | Inline rejection loop unproved | Shared-operand comparison; x ≠ 0 a.s. |
| `Occil.PSRN.newTulap` | Inline rejection loop unproved | No support exists |
| `Occil.PSRN.newFGMCopula` | Rejected: no fitting spec kind | Returns a pair; `latent_vector` needs a list |
| `Occil.PSRN.newRectellipse` | Rejected: no fitting spec kind | Same; see [vector notes](ExactPSRNVectorRejectionProgress.md) |

The pair-output samplers need a protocol decision first: either a pair spec kind or a vector
spec generalized over output encoding, plus an auditor extension.

Unfinished files from the stopped provers were moved out of the tree. The pre-existing,
unimported `SampLib/PSRNGammaCore.lean` was edited during the stopped gamma work. It builds
cleanly on its own, but it is not in any receipt closure or the root build and was not reviewed.
