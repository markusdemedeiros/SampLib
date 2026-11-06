# Exact low-probability source repair review

Author of the canonical patch: `/root`. Independent reviewer: `/root/review_exact_a`.

The reviewed patch changes only the inner margin of
`Occil.FactoryExtra.linearLowProbability` in `code/Samplers/Bernoulli/Linear.lean`:

```diff
-          &linear coin (a * n) (b * #2 * m) (n - m) n #()
+          &linear coin (a * n) (b * #2 * m) #1 #2 #()
```

Original source SHA256: `e0c0cd611bc5a01ab1a5cd68eab7b702a84b903c31d753c1c3e9107fe23c1217`.
Resulting source SHA256: `9c9490a35bbb29cc233101e66d6a3c27bb0fb018ab15ce204950e1fdc13027cf`.
The byte-exact original is archived in [ExactLowProbabilityOriginalSource.txt](ExactLowProbabilityOriginalSource.txt).
The old substring occurs exactly once; applying its exact replacement leaves every
other source byte, definition, guard, callback and branch unchanged. In particular,
contracting and zero-upper-bound behavior is retained. No language or dependency
change is part of this repair.

## Domain and mathematics

Write μ=(a/b)p and ρ=m/n. On the expanding nonzero branch the advertised domain
is 0<ρ<1/2 and μ≤ρ. The inner linear bias is μ/(2ρ), hence at most1/2.
The old margin1−ρ incorrectly demanded μ/(2ρ)≤ρ. The replacement margin1/2
is justified on the complete advertised domain. Both the logistic and rational
selectors remain unchanged; their mixture cancels to the target probabilityμ.
All nonnegative contracting and zero-upper-bound cases are covered separately.

The formal source sibling `SampLib.LowProbabilityRepair.algorithm` differs from
the canonical source by exactly this patch. Its complete public theorem
`SampLib.LowProbabilityRepair.lowProbabilityRepair_distSpec` was independently
reviewed after two presentation passes: the syntax opening now uses checked beta
steps and a small closed-source normalization; the main CTE argument is direct
branch execution under named callback specs; the mixture expectation argument
is separate and supports arbitrary extended nonnegative credits.

Independent caller: [ExactLowProbabilityRepairCallers.lean](ExactLowProbabilityRepairCallers.lean).
It compiled without warnings/errors, retaining arbitrary Iris resources and
arbitrary input callbacks. It exercises the old defect boundary, a zero upper
bound, a contracting boundary and infinite credits. Public spec, CTE, expectation
and margin theorems print only `propext`, `Classical.choice`, `Quot.sound`.

This approves the exact source repair. It does **not** accept the original
unrepaired sampler, promote the sibling as its proof, or renew any historical
transitive proof snapshots. After applying the patch, the canonical/sibling
equality and canonical public specification must compile, affected current
receipts must be renewed, and the216-entry historical suite needs its explicit
source-change compatibility overlay. The margin counterexample alone proves a
contract mismatch; the older exact-rational certificate separately witnesses
the original output-law error.
