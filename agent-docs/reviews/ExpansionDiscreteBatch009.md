# Expansion discrete review: immutable batch 009

Reviewer: `/root/expand_review_discrete`. Three accepted core samplers.

## `Occil.DiscreteExtra.borel` — accepted (core)

Public specification: `SampLib.Borel.borel_distSpec`.

Source SHA-256: `17f74a5ab0c282992a7af40216e79c041ebe5417906c8a58e0e2d93f4952ae4a`.

The independent target is total progeny of a Poisson Galton–Watson tree, constructed from increasing finite-height tree measures. Finite-forest continuity uses diagonal cofinality; branching yields extinction mass q=exp(r(q-1)), and subcriticality forces q=1. This is not a queue-absorption recurrence definition. The CTE proof explores one root, uses the forest branching credit identity and Poisson offspring mean, and pays for termination with pending-population potential and amplification2-r. Independent tests check the first height-truncation mass exp(-r), zero-rate Dirac1, no zero progeny including infinite credit there, normalization, infinite expectation and generic framing. No explicit classical factorial-PMF identity is claimed.

## `Occil.WeightedVariants.oneillUniform` — accepted (core)

Public specification: `SampLib.OneillUniform.oneillUniform_distSpec`.

Source SHA-256: `96438d9aeca9dc85777d138afcd513cc34b1125b4ed8d8e26c6033f76a3991a8`.

The canonical uniform target reuses Lemire equal-fibre expectation. A fresh-product rejection wrapper and current-product wrapper isolate the retry logic. The initial low-word>=n case skips threshold evaluation safely because the Euclidean remainder is<n. Otherwise a deterministic helper proves the one-subtraction, two-subtraction and modulo-fallback thresholds all equal width%n. Independent clients instantiate n5/width8, n3/width8 and n3/width16, plus n=width and zero-bit singleton, and frame arbitrary resources with arbitrary ENNReal credits.

## `Occil.DiscreteExtra.fisherHypergeometric` — accepted (core)

Public specification: `SampLib.FisherHypergeometric.fisherHypergeometric_distSpec`.

Source SHA-256: `958e20723d8bb8893f5b1990b4bd4f12375ecd5e6b5216c1693eb25372753a97`.

The independent canonical Fisher PMF is proportional to choose(ones,k)*choose(zeros,n-k)*a^k*b^(n-k), zero outside0..n. A feasible k=min(n,ones) proves a positive normalizer. Deterministic program helpers execute four exact choose/power calls in their actual evaluation order and build the complete finite table; main CTE validates, builds and delegates to categorical sampling. Tests check arbitrary empty draws, both exhausted-color boundaries, complete population, and the odds2/1 example with ones2/zeros1/n1 giving marked probability4/5. Infinite credit at an impossible count and generic framed clients are checked.

## Supporting mathematics

GaltonWatson defines height truncation independently of exploration order, proves monotonicity and finite-forest continuity, then normalizes the finite-progeny limit from its generating-function fixed point. Conversion to real arithmetic is confined to its scalar extinction mass q<=1, never an arbitrary continuation. PoissonGenerating sums the nonnegative exponential series; a separate size-bias factorial identity gives the offspring mean directly in ENNReal. Boundary lemmas identify zero-rate total progeny and exclude zero progeny.

FisherWeights clears a common odds denominator and proves the finite table has positive total. FisherHypergeometric exposes the exact standard singleton masses and their normalized measure. Its zero-measure invalid-input case is replaced by an explicit harmless Dirac extension; public sampler specifications use the full valid domain.

Support hashes:

- `SampLib.Distributions.GaltonWatson`: `2af0e4c196ff938319f566e05c6098db0955d8fc91ae7bbfeb012996546921c6`.
- `SampLib.Distributions.PoissonGenerating`: `d13ef5bb7a1485f3af57ae16555e696400d0d42232a9b75d31bc8aa63a9c9516`.
- `SampLib.Distributions.FisherWeights`: `4b182c51fc8bf6c39a9d110e205c44e4e99209ff43e553b603abf5711bdc795f`.
- `SampLib.Distributions.FisherHypergeometric`: `919fdbc89008ef6990e3cfb7090c5e539f24d5cbe5b25920422b908affa91f31`.

## Validation

Independent gated three-module build passed without warnings (4269 jobs). Working and immutable copied clients compile without warnings. Public specs, central expectation lemmas, branching/normalization/credit recurrence, Poisson mean/generating function and Fisher PMF/positivity depend only on propext, Classical.choice and Quot.sound. Source widths and whitespace pass. All targets are normalized with typed integer encoders, arbitrary measurable ENNReal credits and unrelated resources retained through calls.
