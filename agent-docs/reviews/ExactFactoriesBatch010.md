# Exact factories batch010: post-repair source revalidation

Independent reviewer: `/root/review_exact_a`.

The repaired low-probability wrapper is in a source file imported transitively by
these two algorithms. Neither direct sampler, its proof, mathematical law,
parameter domain, encoder nor callback interface changed. I independently compared
the complete old and current project-local source snapshots: their file sets are
identical and only the approved Linear.lean hash differs. The exact patch changes
only a declaration called by neither of these sampler implementations.

I rebuilt POverTangent and ArctanOverPi separately against the repaired code and
then compiled the new independent caller. All three commands passed cleanly.
The caller preserves arbitrary Iris frames and credits, including infinity,
exercises the complete abstract callback domains, supplies a concrete p=1 positive
tangent-gap witness, checks the excluded zero tangent endpoint, and verifies the
arctangent endpoint probabilities. The mathematical and program-logic source
reviews from batches004 and006 remain valid; this receipt binds them to the fresh
compiled source context without editing either earlier receipt. Both entries
remain derived constructions, not additional algorithms.

## Accepted sources

- `Occil.FactoryExtra.pOverTangent`: `SampLib.POverTangent.pOverTangent_distSpec`; SHA256 `0899376099784974a5f10d4ae5dcaa8a52d3244a8a9dafc2f862f6d3d1483e31`.
- `Occil.FactoryExtra.arctanOverPi`: `SampLib.ArctanOverPi.arctanOverPi_distSpec`; SHA256 `77cb98bf852a3a85d92b30625e1d7b154dcd03098d697da85c7e2cd3852c1810`.

## Evidence

Independent caller: [ExactFactoriesBatch010Callers.lean](ExactFactoriesBatch010Callers.lean).
The new receipt records the full current source closure and dependency context.
The printed public specifications use only `propext`, `Classical.choice`, `Quot.sound`.
The implementation patch approval is [ExactLowProbabilitySourceRepair001.md](ExactLowProbabilitySourceRepair001.md).
