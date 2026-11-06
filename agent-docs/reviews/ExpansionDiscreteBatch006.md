# Expansion discrete review: immutable batch 006

Reviewer: `/root/expand_review_discrete`. Two accepted core samplers.

## `Occil.DiscreteExtra.multivariatePoisson` — accepted (core)

Public specification: `SampLib.MultivariatePoisson.multivariatePoisson_distSpec`.

Source SHA-256: `c3fc64a8636b7bbb6d0633166bc31a6cbeadc5d8b70d15307b5a44d1dbf6010f`.

The independent target conditions on one shared Poisson count, then takes a product of independent residual Poisson counts, shifting every coordinate by the same common count. Product and mixture expectations are separated from finite-list CTE execution. Tests check the empty-list Dirac law, two zero residual rates giving [shared,shared], arbitrary infinite expectations and generic framed clients with the actual list encoder.

## `Occil.DiscreteExtra.logUniform` — accepted (core)

Public specification: `SampLib.LogUniform.logUniform_distSpec`.

Source SHA-256: `b7ee2f5b1983912e261bab51e2e7bbbbf9af2c21b74e2d02fbf845bc4d5e2837`.

The canonical finite mixture chooses each logarithmic magnitude level equally; zero has its own bucket, positive buckets are inclusive power intervals, and the final bucket is clipped to the inclusive maximum. This is an exact integer bucket law, with no continuous log-density claim. Named natural-log inequalities prove all positive buckets are valid. Deterministic ceiling and integer-power helpers keep the CTE proof symbolic. Tests check maximum0 Dirac0, base2 maxima7 and8 bucket boundaries, exact mass1/5 at the clipped final singleton8, arbitrary infinite expectation and framed clients.

## Supporting mathematics and syntax

LogUniformBuckets uses the standard natural ceiling logarithm to identify valid finite magnitude intervals. ClosedExp explicitly requires both local closedness and empty free-variable set. Its two nonglobal rewrite rules are direct applications of existing open_lc and closeRec_fresh lemmas. Independent tests build a closed identity expression, normalize three nested binder operations, and show an arbitrary free-variable expression cannot satisfy the class. No instance is inferred for all locally closed expressions.

Support hashes:

- `SampLib.Syntax.ClosedExp`: `0779879220a63feed000a472b6d85ee60eec3bbd7e77f7b50b5d2b0a82004d30`.
- `SampLib.Distributions.LogUniformBuckets`: `44e57f096ad1c47bb86708e434f1f5d1e69e6cdb49cb55169e19107a3747b6b7`.

## Validation

Independent gated module build passed without warnings. Working and immutable copied callers compile without warnings. Printed public specifications, expectation lemmas and syntax rewrites depend only on propext, Classical.choice and Quot.sound. All new Lean sources have at most100 columns and clean whitespace. All specifications accept arbitrary measurable ENNReal credits and retain unrelated Iris resources.
