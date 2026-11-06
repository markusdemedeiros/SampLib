# Exact structured sampler review, batch 005

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.InclusionSplitting.inclusionSplitting_distSpec`, SHA-256 `3fcca04ecfbbae4bb28038827e9cf436b85f25ed1935589b41b6b168af70465f`.

Domain: All positive-total natural weights, count≤population length, and count*weight≤total at each position. Includes zero weights, full samples and capacity equality. A separate zero-count theorem covers every natural-weight list, including empty/all-zero populations, without uniform-integer assumptions. The target is the exact ordered full joint splitting law, with fixed size, no duplicates and prescribed inclusion probabilities.

## Mathematical law and termination

A state has sorted labelled integer inclusion numerators, total count times a
positive common denominator and every numerator bounded by that denominator.
Its interior split amount is positive and at most the denominator. Acceptance
selects the upper count labels; positive-probability rejection subtracts the split
from those numerators, reorders and strictly decreases the natural denominator.
This defines a finite normalized mixture law on the FULL ORDERED output lists.
The terminal split amount equals the denominator and accepts with probability one.

The single split expectation is the accepting credit plus residual-law credit.
It holds for arbitrary ENNReal continuations including infinity. Separate
integer numerator-credit decomposition proves the prescribed inclusion marginals
without ENNReal subtraction. Length and distinctness follow through the finite
mixtures and original-label permutations; full and zero samples are handled
separately. The root-authored marginal helper was independently reviewed, built
and axiom-checked in ExactSplittingMarginals001 before this concrete acceptance.

## Actual CTE source

Review covered stable insertion, source preprocessing, exact residual adjustment,
upper-block list selection, source-opening certificates and the main proof.
The symbolic round does its two source lookups, exact minimum, rational coin and
the corresponding deterministic branch. The supported coin rule rules out false
at a terminal probability-one split, so no zero-denominator successor is assumed.
Natural denominator induction supplies actual rejection continuations. The outer
source executes validation/preprocessing and respects the exact prepared-list
order in its full-count branch. Mathematical expectation facts are separate;
no desired concrete sampler law or termination premise appears. Runtime source
and previously accepted proofs remain unchanged.

## Independent validation

Targeted build, exact-head/noncircular signature audit and caller pass warning-free.
The independent fixture retains arbitrary F on WHOLE output lists and an unrelated
Iris resource. Empty/all-zero zero-count requests require no UniformInt. A sparse
interior population exercises immediate terminal probability-one acceptance;
a full-count caller uses infinity. Capacity equality and ordinary residual
rejection are exercised on weights [1,2,1] with count2.

For that last population the fixture proves the exact ordered joint law:
one half at [2,1], one half at [0,1]. Thus the middle position is certain, the
edges never co-occur, and source ordering is checked in addition to marginals.
All six public sampler/marginal/size/distinctness axiom checks use only propext,
Classical.choice and Quot.sound. ExactStructuredBatch005.log retains commands
and outputs. The immutable receipt binds the full local support closure,
independent caller and current clutch06a7b3e dependency context.
