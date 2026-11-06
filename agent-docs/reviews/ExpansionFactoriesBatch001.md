# Factory expansion review: batch 001

Reviewer: `/root/expand_review_factories`.

All three modules passed independent targeted builds without warnings. The immutable caller artifact compiles without warnings and prints only `propext`, `Classical.choice`, and `Quot.sound` for the nine inspected mathematical/program theorems. Caller checks include arbitrary framed resources, parameter boundaries, infinite credits, and a concrete composed sampler.

## Occil.FactoryExtra.oneDivTwoMinus

Accepted `SampLib.OneDivTwoMinus.oneDivTwoMinus_distSpec`, SHA-256 `836af4d2489dd0cd4d673240b286c461a2de296ae553b27de298020dbc0b08bb`.

Complementing the supplied input gives bias 1-p, then the verified reciprocal factory gives 1/(2-p). The coefficient identity is explicit. The CTE proof executes the wrapper and composes its verified callback. The shared structural callback preserves arbitrary callback free variables. Independent callers frame an arbitrary resource, cover p=0 and p=1, assign infinite credit off the deterministic p=1 support, and compose with the concrete fair coin.

## Occil.FactoryExtra.reciprocalLogistic

Accepted `SampLib.ReciprocalLogistic.reciprocalLogistic_distSpec`, SHA-256 `3ae5c4a2c9c4fa3875299e427fc607371299e119816280685cf9cda7c57e8857`.

The positive-coefficient branch complements the verified logistic factory. Its central expectation lemma transports the complement law to b/(b+a*p); the zero coefficient returns true directly. The CTE proof only executes that guard and the verified call. Independent callers cover the zero coefficient for arbitrary p, a nontrivial rational endpoint bias, arbitrary framed resources, and infinite credit outside the deterministic zero-coefficient support.

## Occil.FactoryExtra.integralMixture

Accepted `SampLib.IntegralMixture.integralMixture_distSpec`, SHA-256 `2d01a1d68e555a94748108e4b44e10fa8aaf99269ea7146f7380d9a0d099a01d`.

The normalized target is the integral of the supplied conditional probability kernel against the parameter law. The single mathematical identity is Tonelli/the tower identity for arbitrary ENNReal credits. The program proof consists of the parameter call followed by the corresponding conditional callback. The contract does not replace conditional callback specifications with unconditional marginals. Independent callers retain an arbitrary resource over any measurable parameter space and check infinite off-support credit for a deterministic conditional kernel.

## Shared support

`SampLib.CoinComplement` was independently reviewed: its structural lambda makes one fresh supplied callback call, applies the complement expectation identity, then returns Boolean negation. It introduces no callback-freshness restriction or extra randomness. Its transitive source is pinned by the accepted specifications.

The immutable caller artifact is `agent-docs/reviews/ExpansionFactoriesBatch001Callers.lean`, SHA-256 `dc180ac020c731e8d0c904bc14832cc70f61412cfaf4bbcc94d425932bc0b3d2`.
