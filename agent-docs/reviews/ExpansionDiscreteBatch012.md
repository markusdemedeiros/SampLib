# Expansion discrete review: immutable batch 012

Reviewer: `/root/expand_review_discrete`. Two accepted core samplers.

## `Occil.Weighted.rationalChoice` — accepted (core)

Public specification: `SampLib.RationalChoice.rationalChoice_distSpec`.

Source SHA-256: `f00ed8bd4d4c6855cd638a2e9483abc0abcf7aa8bcea9ed03e8647a3ef187b03`.

The independent categorical characterization is each input rational weight divided by its rational total. Exact common-denominator scaling preserves arbitrary ENNReal expectations, including infinite output credits. Main CTE validates denominators, computes their product, converts the rational weights exactly to integers, and delegates to verified categorical sampling. Independent tests give probabilities 3/5 and 2/5 for weights 1/2 and 1/3, permit unreduced 2/4, retain arbitrary singleton credit for 7/13, eliminate infinite credit at zero-weight slots, and preserve an unrelated framed resource.

## `Occil.Weighted.uniformBinaryFloat` — accepted (core)

Public specification: `SampLib.UniformBinaryFloat.uniformBinaryFloat_distSpec`.

Source SHA-256: `3c0aedda462e07b3cade01880c97642507a658e2b61f020ad1642455129c3696`.

The exact finite-format law decodes an independent capped fair-geometric leading-zero count and uniform mantissa into an integer significand/exponent pair, returning(0,0) at the cap. It makes no continuous-uniform or IEEE claim. Fubini and the capped-geometric split supply one expectation identity. The CTE proof inducts on the remaining zero cap, draws a fair bit, then either advances the prefix or draws the verified random-bit mantissa and deterministic binary power. Independent precision 2/cap 2 tests give zero-output mass 1/4, point(4,-3)mass 1/8 and point(7,-4)mass 1/16; cutoff(4,-5)has zero mass even with infinite credit. Zero precision/cap, normalized infinite expectation and generic pair-valued framing are checked.

## Supporting mathematics and deterministic code

RationalChoice exposes exact rational-weight expectations and singleton probabilities, independent of the common integer scale. WeightedSums handles all-zero blocks without canceling arbitrary infinite continuation values. DiscreteLaplace uses explicit residue/quotient bijections and nonnegative exponential sums to identify the accepted law; FisherMultivariate exposes the standard product coefficient, positive normalizer, conditional restriction and exact support; only finite scalar mass enters real arithmetic, never an arbitrary continuation.

NatUrnOps is deterministic supporting code, not another sampler. Its validator accepts matching natural populations and positive odds; its weight routine truncates to population length and computes pointwise products. Independent callers omit UniformInt, frame arbitrary resources, include zero capacities and test an extra ignored odds suffix. UniformBinaryFloat independently combines standard capped-geometric and finite-uniform laws; its product-law split gives the program expectation. SamplerStep constructs the existing checked pure-step/context rule with a caller-controlled symbolic reduct; source review confirms no trust extension, and public sampler axiom checks remain standard.

Support hashes:

- `SampLib.Distributions.RationalChoice`: `24ab77d012f9e0d1e776fa1e9a0bfbfd4943c9156ed59958f1872cb8df0e6bcc`.
- `SampLib.Distributions.WeightedSums`: `9760cbf10638c77224a5d061ca2ad9aa6fd55a803e0abc1d0a1819b6ffeb461e`.
- `SampLib.Distributions.DiscreteLaplace`: `7030d9a2dbe32b43f8cc5e4dcd1abe032e9958fe6a07e8247556053642bafe13`.
- `SampLib.Distributions.FisherMultivariate`: `eb9f6e601d9efe972847ac69b6ec2b2b61285cba371ceb28baeaffd2de08009a`.
- `SampLib.NatUrnOps`: `e846b9bb2b12f9a4bff876b1773e59a4607a7e35f0bcca7a60f906d311a614bb`.
- `SampLib.Distributions.UniformBinaryFloat`: `8b573967e00bb8e6a846565fbda0e2e95d03a6154b5a64a161224fbbd9fe38a9`.
- `SampLib.SamplerStep`: `a3e143551b2719b11170456de08e0c193059c00b6b8dafabe3c747c03eb52335`.

## Validation

Independent gated module builds passed without warnings (4162 jobs in the combined target build). The frozen canonical DiscreteLaplace/FisherMultivariate analytic laws and NatUrnOps are independently reviewed and tested supporting results for upcoming consumers; those actual samplers are not accepted by this receipt. Working and immutable copied clients compile without warnings. Public specs, central expectation lemmas, analytic identification, exact singleton proportions, accepted-proposal conservation and support lemmas depend only on propext, Classical.choice and Quot.sound. Source widths and whitespace pass. All targets are normalized with typed integer encoders, arbitrary measurable ENNReal credits and unrelated resources retained through calls.
