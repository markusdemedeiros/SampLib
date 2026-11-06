# Expansion discrete review: immutable batch 001

Reviewer: `/root/expand_review_discrete`. All three sources, this receipt, and the
matching caller artifact are frozen. Existing 47 baseline proofs are unchanged.

## `Occil.DiscreteExtra.betaBinomial` — accepted (derived)

Public specification: `SampLib.BetaBinomial.betaBinomial_distSpec`.

Source SHA-256: `7adba19877f3d7befb872af29cb1231c57e7a9eaf54cfbdf6aa9aaee1f9a6cd5`.

The law is the verified reinforced urn with common-denominator shapes a*d, c*b and reinforcement b*d. Its inherited rising-product word masses give the beta-binomial characterization. The CTE proof checks rational domains, clears denominators, and applies the verified urn specification. This is a derived named-law specialization; its mathematical argument is inherited rather than duplicated. Independent callers cover arbitrary resource framing, zero trials, infinite credits, and one trial with shapes 2/3 and 5/7, whose success mass is 14/29.

## `Occil.Weighted.randomBits` — accepted (core)

Public specification: `SampLib.RandomBits.randomBits_distSpec`.

Source SHA-256: `803dad79aafcb0914d543ab87e3cd3266f4446f2b3b897640c9a2b13701feb62`.

The target is the existing canonical finite uniform law. A prefix followed by a binary suffix gives one uniform integer block; the central expectation identity partitions that block into two equal halves. Arbitrary ENNReal credits are retained throughout, with no cancellation or real-valued conversion of credits. Symbolic execution is finite induction, one fair integer bit, and the recursive call; binder normalization is isolated from the interval mathematics. Independent callers cover the empty word, arbitrary bit counts, infinite credits, and preservation of an arbitrary caller resource.

## `Occil.DiscreteExtra.symmetricGeometric` — accepted (core)

Public specification: `SampLib.SymmetricGeometric.symmetricGeometric_distSpec`.

Source SHA-256: `e41632a20e58190c2d2f9c217602b30816b4da79b345e949d18820add02d1a9c`.

The product construction is identified independently by its normalized atom masses: q^n*p/(2-p) at n and q^(n+1)*p/(2-p) at -1-n, with q=1-p. These establish reflection and the p=1 Dirac-zero limit. The sole credit identity is product integration; the CTE proof samples the geometric magnitude, composes the complemented-coin reciprocal selector, and returns its signed placement. I requested explicit tail characterization and a line wrap; both were addressed. Independent callers check reflection, p=1, infinite credits, callback composition, and arbitrary resource framing.

## Supporting callback rule

`SampLib.CoinComplement.distSpec` has been independently reviewed and tested with
an arbitrary framed resource. It negates exactly one fresh invocation of the
supplied callback and reuses the existing complement expectation identity. Its
source SHA-256 is `1b7b26efc1723bb575ea6f3d9e5effc8b92c8f89f2e01d686c34b1ea9a78de56`.

## Validation

The independent gated module build completed successfully (4161 jobs), without
warnings. The copied `ExpansionDiscreteBatch001Callers.lean` compiles without
warnings. Public specs, the new binary expectation and tail mass lemmas, and the
callback rule depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Whitespace checks and the 100-column target pass.
