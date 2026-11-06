# Factory expansion review: batch 002

Reviewer: `/root/expand_review_factories`.

All eight new modules passed independent targeted builds without warnings. The immutable combined caller artifact compiles without warnings and prints only the three standard axioms for all 33 inspected theorems, including the three preceding batch specifications. The accepted count below includes only the eight new samplers.

## Occil.FactoryExtra.positivePowerSeries

Accepted `SampLib.PositivePowerSeries.positivePowerSeries_distSpec`, SHA-256 `d74b1edf3246645dedfe30981a35c00e836c974d0bc0095f9af07babb612a862`.

The law mixes all-successes coins against normalized coefficient weights. Its explicit success atom is the finite coefficient-weighted polynomial, including the constant term. The central PGF expectation is reused rather than re-expanded. The CTE proof selects the degree and composes IterateCoin. Independent clients retain arbitrary resources; coefficient and bias endpoint tests include a zero-weight constant term with infinite success credit.

## Occil.FactoryExtra.complementPowerSeries

Accepted `SampLib.ComplementPowerSeries.complementPowerSeries_distSpec`, SHA-256 `0475f0036b3fa368bae64cc76c9f79fb644ffa0ea96ca76fffe8ff769cba844c`.

The target polynomial contains exponent i+1, matching the runtime increment. Conditioning on the exponent and the verified complement expectation give the full ENNReal conservation identity. The CTE proof composes categorical sampling, fresh complemented callbacks, IterateCoin, and output negation. Independent callers check arbitrary framing, the singleton-coefficient identity law, and infinite off-support credit at p=1.

## Occil.FactoryExtra.complementLogInverse

Accepted `SampLib.ComplementLogInverse.complementLogInverse_distSpec`, SHA-256 `d93f89dfc2f97650d9c99842f14b508109bf5ea5da1217680643f54bf63143e2`.

This is the verified logarithmic factory applied to a fresh complemented callback. The explicit bias identity identifies the named function; the p<1 condition is precisely positivity of the complemented geometric success bias. Program execution is a wrapper plus the known callback specification. Independent clients frame arbitrary resources and cover the p=0 zero-bias endpoint with infinite success credit.

## Occil.FactoryExtra.convexCombination

Accepted `SampLib.ConvexCombination.convexCombination_distSpec`, SHA-256 `da23cbeaabdc5dd287631189d172197fdb10b247a53b379335c33da3b431a14c`.

The normalized measure is a categorical mixture of the specified component Bernoulli laws, with an explicit weighted-average success atom. A categorical support lemma justifies assigning infinite credit outside the callback list; no probability or continuation credit is cancelled there. The main logic follows selection, deterministic lookup, and the selected callback. Requested polish replaced arithmetic search on list lengths with direct equality transport. Independent clients check framing, a fair mixture of deterministic component endpoints, and zero weights with infinite off-support credit.

## Occil.FactoryExtra.oddsProduct

Accepted `SampLib.OddsProduct.oddsProduct_distSpec`, SHA-256 `aed9028b5993bb1a3d4c0f6bb28f3aa21b538fc1764fa5e5f4d6479cd0b709a4`.

One trial has accepted true mass mu*p, false mass 1-mu, and retry mass mu*(1-p). The reusable BernoulliRetry balance identifies the normalized accepted bias and bounds amplified retry credit. The CTE proof reads the selector and input coin, returns on either exit, and explicitly splits credit on retry. The condition excludes only the nonterminating pair selector one/input zero. Independent clients frame arbitrary resources and check selector zero, selector one with positive input, and infinite credit outside the zero-selector support.

## Occil.Constants.fromDigits

Accepted `SampLib.FromDigits.fromDigits_distSpec`, SHA-256 `4fa8a1549f97d05a90deaa9373ebb5262ee6e53a937cf4717bb2cf7ba66e3fcc`.

The canonical target probability is Real.ofDigits of the supplied expansion. The mathematical lemma partitions a uniform digit into below/equal/above cases, uses the standard radix-tail identity, and accounts for retry probability 1/base with amplification two. The deterministic digit contract uses one-based runtime indices and the corresponding zero-based expansion; this indexing was checked explicitly. The structural recursive body preserves arbitrary oracle free variables. Independent clients cover arbitrary framing and both infinite endpoint expansions, including infinite credit outside their deterministic output supports.

## Occil.expMinusRational

Accepted `SampLib.ExpMinusRational.expMinusRational_distSpec`, SHA-256 `9c1ca55cc40734cad464c69f26b2eb9c053eb96f3353806f5d2910f869c43b26`.

The shared factorial-trial mathematics computes products of hazards t/i and identifies their exit masses with the established decreasing-chain factorial differences. Even/odd mass gives exp(-t). The first trial is separated from the uniformly terminating tail i>=2; no endpoint is lost. The outer finite product implements the integer part, and an explicit Euclidean-division identity identifies the final rational exponential. Each CTE helper follows that natural program boundary with simple execution and known specifications. Independent clients check resource framing, zero, an integral argument, a proper fractional remainder, and infinite off-support credit at argument zero.

## Occil.FactoryExtra.approximateFactory

Accepted `SampLib.ApproximateFactory.approximateFactory_distSpec`, SHA-256 `191f529936ef9567d92e45b97082673eaf6b974cf1492b698f99911596af868f`.

The target is the actual binomial mixture of clamped integer-grid evaluator outputs, with an explicit finite Bernstein success formula. No claim identifies this probability with f(p). The evaluator contract is required only for Fin(trials+1); infinite off-support credit removes impossible counts. Deterministic clamping is isolated from the main program proof. Independent clients retain arbitrary resources and test both out-of-range clamping directions with infinite off-support credits. A rounding-sensitive check proves that two trials, scale one, and the identity evaluator yield bias p^2.

## Shared support

All listed support was independently read. BernoulliRetry isolates accepted exit masses and a bounded amplification factor; its balance uses only finite real coefficients and leaves arbitrary ENNReal continuation credits untouched. Digits reuses mathlib's radix-tail identity. AlternatingFactorial reuses the established factorial parity calculation after an explicit finite-product identification. WeightedSupport derives categorical support from the point-mass formula. FactorySyntax consists only of closedness identities; CoinComplement is the reviewed structural fresh-callback adapter.

The immutable caller artifact is `agent-docs/reviews/ExpansionFactoriesBatch002Callers.lean`, SHA-256 `6a74fb89edca499e713cce006b2c006efa6bb3c17131736353006c4b432cbed2`.
