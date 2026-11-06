# Expansion discrete review: immutable batch 004

Reviewer: `/root/expand_review_discrete`. Two accepted core samplers.

## `Occil.poissonRational` — accepted (core)

Public specification: `SampLib.PoissonRational.poissonRational_distSpec`.

Source SHA-256: `2eb51e39762c7a31e000c5eff5b9c209271d6d915ebf5ad036a3b6ffb1598a66`.

Independent Poisson additivity handles unit-rate draws; independent binomial thinning handles the final fractional rate. The single expectation theorem identifies both cases with canonical Mathlib Poisson(x/y). The remaining-rate loop is straightforward strong induction. Tests explicitly establish real rate(1,2)=1/2, rate(6,2)=3 and zero rate, check thinning endpoints p=0 and p=1 plus the fractional case, infinite continuation values and arbitrary resource framing.

## `Occil.Weighted.bitmaskRejection` — accepted (core)

Public specification: `SampLib.BitmaskRejection.bitmaskRejection_distSpec`.

Source SHA-256: `e98aa456308db2f3b9143ef681144bd1e071590d61f438e7dc11adb889cf4ef4`.

The enclosing width is the least power of two covering the target interval. A private binary-word loop reuses the reviewed RandomBits prefix expectation. Accepted words preserve exactly the canonical uniform target credit; at most half the enclosing words are rejected, funding retry amplification by two. The obvious CTE retry loop follows this inequality. Tests cover widths1/4/5, the exact no-rejection kernel at power-of-two width4, infinite off-support credit at width1 and arbitrary framed callers. The candidate helper remains private in the same file, keeping its elementary component proof next to its use.

## Supporting mathematics

PoissonThinning proves the canonical Poisson/binomial mixture directly through factorial cancellation and the exponential series; only finite nonnegative coefficients enter real arithmetic. It also exposes canonical independent Poisson additivity. PowerOfTwoCeiling proves exact deterministic preprocessing and the enclosing-width bound. UniformRejection splits a finite interval into accepted and rejected ranges, preserving arbitrary ENNReal target expectation and bounding retry credit.

BinomialThinning was independently reviewed for another author: finite reflection, direct paired-coin thinning, filling by complement and support, finite mean, and endpoint Dirac laws. Its support hypotheses justify all natural subtraction. Independent tests check thinning probabilities zero and one, arbitrary infinite credits, and mean one for two fair trials.

Support hashes:

- `SampLib.Distributions.PoissonThinning`: `46acd71a9d7ea898a1903a8c3a20b94e27c9cb3bdbe7706a14f0023e0a3e7223`.
- `SampLib.PowerOfTwoCeiling`: `32bf9a0364af8c7436791407afb4214ac0545f07cac790613b30db4099fdf2cb`.
- `SampLib.Distributions.UniformRejection`: `1004d8fecd12a5c8c46027026700f0d60b1919cac6ba9e40254dffb353383da0`.
- `SampLib.Distributions.BinomialThinning`: `ccd9bb7dacc5de34badde21688c5319c594e6f87c7da9665173b90b06943f704`.

## Validation

Independent gated module build passed without warnings (4252 jobs). Working and immutable copied callers compile without warnings. Public specifications and central helper lemmas depend only on propext, Classical.choice and Quot.sound. All new sources have at most100 columns and clean whitespace. Arbitrary measurable ENNReal continuation credits are supported throughout.
