# Expansion discrete review: immutable batch 013

Reviewer: `/root/expand_review_discrete`. Three accepted core samplers.

## `Occil.DiscreteExtra.fisherMultivariate` — accepted (core)

Public specification: `SampLib.FisherMultivariate.fisherMultivariate_distSpec`.

Source SHA-256: `132ffcee7fdca3a9c73103190ca2d4953eb99b553cc5a3a38b1f2838c0eece7b`.

The canonical law conditions independent odds-matched binomials on the requested total; its standard product-coefficient PMF, positive normalizer, support and endpoint laws were independently reviewed and tested in Batch012. The proposal builder samples each binomial once. A single accepted-proposal expectation inequality funds amplified retries after checking the sum. Actual zero and full-population shortcuts return the corresponding deterministic count vectors. The small private constructor helpers insert verified constants after structural binders, avoiding unnecessary closure traversal; the public theorem still checks the unchanged actual source. New independent callers frame arbitrary resources and arbitrary ENNReal continuations through the whole program, and exercise empty/full shortcuts with exact literal count-vector encoders.

## `Occil.WeightedVariants.twoLevelChoice` — accepted (core)

Public specification: `SampLib.TwoLevelChoice.twoLevelChoice_distSpec`.

Source SHA-256: `1ea1cd5dc891be211b307ce3670cfd2c25c726839a13823d05754d3bebce02d2`.

Consecutive chunks partition the original categorical weighted sum. Selecting a block by its total and a label by its conditional weight cancels the block total; an all-zero block contributes zero even for infinite output credits. The single expectation identity identifies the result with the independently normalized canonical WeightedChoice law. Main CTE validates, groups and totals the data, draws a supported positive block, looks it up safely and performs the conditional categorical draw. Independent tests include a leading zero-total block, a short final block, size one and size larger than the list. Infinite credits at zero-weight labels reduce to the finite expected value8/5; generic callers retain arbitrary framed resources.

## `Occil.Weighted.fyky` — accepted (core)

Public specification: `SampLib.FYKY.fyky_distSpec`.

Source SHA-256: `a277b34bbb9b81d547ba3c5a9a975f119ea6288d62ca92cf3f9a2aaffb3869f4`.

The public target is the independently normalized UniformInt law. Individual retained states follow finite-horizon continuation credits, rather than an incorrect per-state uniform output claim. Appending fair bits enumerates the doubled interval; the upper accepted block emits every target once and the lower residue remains narrower than the target. The aggregate credit bound leaves exponentially vanishing cutoff mass, so an arbitrary positive error budget removes the horizon. Main CTE is finite-horizon symbolic execution, using cutoff credit1 to derive contradiction, plus one initial uniform-credit bound. Independent callers cover non-power-of-two targets3 and5, arbitrary ENNReal continuations and resources, and the singleton without UniformInt. Shared tests distinguish lower and upper orientation states with infinite credit and check exact cutoff tails.

## Supporting mathematics and deterministic code

The canonical FisherMultivariate distribution and NatUrnOps were independently accepted as supporting results in Batch012. This receipt adds their actual Fisher consumer. Syntax/Urns supplies only scoped instances with genuine local closedness and empty free-variable sets; arbitrary callbacks are not assumed closed.

WeightedBlocks proves exact chunk flattening and total preservation, then conditional categorical normalization. Its block-credit identity handles zero block totals separately and never cancels an arbitrary infinite continuation. Partial final blocks are addressed explicitly in the sum-of-chunks identity. The main program proof uses positive-block support to make the second draw valid.

BitRecycler supports the accepted FYKY sampler and upcoming FastDiceRoller consumer; the mathematical helper is not counted as a sampler. Pairing each retained rank with a bit enumerates the doubled interval; deleting either accepted block leaves the same bulk credit. Finite-horizon cutoff tails decay geometrically, and a purely ENNReal horizon choice removes them. Independent tests give cutoff credit1/4 for target3 after two bits and3/8 for target5 after three bits, distinguish the orientations on an infinite per-state credit, and check arbitrary-credit bulk/initial bounds and horizon existence. No individual retained state is claimed uniform.

Support hashes:

- `SampLib.Distributions.FisherMultivariate`: `eb9f6e601d9efe972847ac69b6ec2b2b61285cba371ceb28baeaffd2de08009a`.
- `SampLib.NatUrnOps`: `e846b9bb2b12f9a4bff876b1773e59a4607a7e35f0bcca7a60f906d311a614bb`.
- `SampLib.Syntax.Urns`: `ef1ed8eb8b8535242f54d9153c6f73cabab140c2934683da4ac85fc320f7229b`.
- `SampLib.Distributions.WeightedBlocks`: `5021b59e201a6284ec301f746e3e97fd5c54c2a3decb18a12da8d89fe80fa6c7`.
- `SampLib.Distributions.BitRecycler`: `2a2d0ac5f23a634c9dedfb6e13c9dca85a7d4c862bb97a447ba3e0aecacfce80`.

## Validation

Independent gated module builds passed without warnings. Working and immutable copied clients compile without warnings. Public specs, central expectation lemmas, analytic identification, exact singleton proportions, accepted-proposal conservation and support lemmas depend only on propext, Classical.choice and Quot.sound. Source widths and whitespace pass. All targets are normalized with typed integer encoders, arbitrary measurable ENNReal credits and unrelated resources retained through calls.
