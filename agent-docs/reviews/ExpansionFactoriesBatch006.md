# Factory expansion review: batch 006

Reviewer: `/root/expand_review_factories`.

All five modules passed independent targeted builds without warnings. The immutable caller compiles warning-free, exercises arbitrary resource frames and boundary/infinite-credit cases, and prints exactly the three standard axioms for all 13 inspected theorems.

## Occil.FactoryExtra.expMinusScaled

Accepted `SampLib.ExpMinusScaled.expMinusScaled_distSpec`, SHA-256 `b5ab25fdac2e384759ffbc0d58970dcd2ab23b9fa5c6580d89e7681ec270f22c`.

A concrete verified Poisson(x/y) count selects the number of independent complemented input flips. The canonical Poisson PGF identifies its success atom as exp(-(x/y)*p); the normalized Boolean-law bridge then gives the entire law. The sole expectation theorem conditions on that count and retains arbitrary ENNReal credits. Program logic is the Poisson draw followed by IterateCoin on a fresh complemented callback. Requested polish removed duplicated Boolean complement/extensionality mathematics in favor of BernoulliMixture. Independent callers check arbitrary framing, zero rate, zero input, input one agreement with the rational exponential coin, and infinite credit outside the deterministic-true support.

## Occil.FactoryExtra.tanhScaled

Accepted `SampLib.TanhScaled.tanhScaled_distSpec`, SHA-256 `9afbca862c593d8f8aaba67715915a02da42d782e48056c24a948ed6b38d09c5`.

The established one-minus-over-one-plus factory receives the actual doubled scaled-exponential callback. A finite exponential identity identifies its bias with Real.tanh; no separate expectation calculation is duplicated. Program execution composes the verified callback and outer factory. Independent callers preserve arbitrary resources and check both zero-input and zero-scale endpoints, including infinite success credit at the deterministic-false output.

## Occil.FactoryExtra.sigmoidScaled

Accepted `SampLib.SigmoidScaled.sigmoidScaled_distSpec`, SHA-256 `98e27b89ead9e0ec8bb12ffcbb6122c51e63cd058b464c6022051e0a54905967`.

The signed mathematical split is the logistic complement identity, and the program branches construct the corresponding positive scaled-exponential callback or complement its reciprocal coin. Structural lambdas preserve arbitrary input-callback free variables. Requested polish removed unused denominator-positivity premises from total mathematical identities while retaining the runtime premise in the public specification. Independent clients frame arbitrary resources and check signed rational inputs, zero input, and zero numerator.

## Occil.FactoryExtra.exponentialTwist

Accepted `SampLib.ExponentialTwist.exponentialTwist_distSpec`, SHA-256 `235d2672c3542e7bccd8c432923a5da703e8102cab3be68a721b7be421844362`.

One trial keeps the input bit precisely when it agrees with an independently drawn logistic selector. Accepted true and false masses are p*sigma and (1-p)*(1-sigma); their sum is strictly positive even at both input endpoints. BernoulliRetry identifies the normalized exponential tilt and funds disagreement retries. The program proof is direct symbolic execution, two callback calls, and explicit retry credit splitting. A structural helper preserves all four original recursive arguments and is definitionally identified with the actual source; arbitrary callback free variables are retained. Independent clients check framing, zero-tilt identity, deterministic input endpoints, and infinite off-support credits.

## Occil.FactoryExtra.twoCoin

Accepted `SampLib.TwoCoin.twoCoin_distSpec`, SHA-256 `18a5258cb981590dd6d17268225d80231a69b42e29ef63727c6cce8fc9ae3814`.

A portkey gate first permits an immediate false exit, then a rational selector chooses the input coin whose accepted result determines the output side. The single expectation partitions the two accepted masses and retry event, and reuses BernoulliRetry. The exact exit condition includes zero portkey, absent weighted sides, and portkey one whenever the actually selected accepting mass is positive. The CTE proof follows the three callbacks and return/retry cases without expectation algebra. Independent clients retain arbitrary frames and test zero portkey with infinite success credit, absent sides, certain accepted inputs, and a zero weighted exit despite a positive unused input bias.

## Shared support

All support was independently read. PoissonGenerating evaluates the canonical Poisson count PGF by the exponential series for every nonnegative argument, including arguments above one. Independent clients check zero rate and PGF arguments zero, one, and two. BernoulliMixture, BernoulliRetry, CoinComplement, and SamplerStep remain frozen reviewed support. All credit identities remain in ENNReal, with finite arithmetic restricted to scalar probabilities.

The immutable caller is `agent-docs/reviews/ExpansionFactoriesBatch006Callers.lean`, SHA-256 `acf3177578eddd312fccc5354bbd9d31fa24fe72415f3a4cc52d02aa97fa9c63`.
