# Expansion discrete review: immutable batch 008

Reviewer: `/root/expand_review_discrete`. Three core and one derived samplers.

## `Occil.DiscreteExtra.binomialBinary` — accepted (core)

Public specification: `SampLib.BinomialBinary.binomialBinary_distSpec`.

Source SHA-256: `c2096b4455fda295a0a35f6c468a3170e565d64fed848d480b26829270ba3241`.

Canonical binomial thinning and filling identify the two binary-refinement branches. The expected unresolved population is n/2, funding fixed3/2 error amplification with potential nδ. The CTE proof draws one supported fair-binomial split, follows either branch and applies the same induction hypothesis; ε/(n+1) removes the auxiliary potential. Independent tests check exact nondyadic bias1/3, one-trial atom1/3, mean1 for three1/3 trials, zero-trial and zero/full-bias Dirac laws, the complete two-fair-trial arbitrary-ENNReal expectation, infinite credits and generic framing.

## `Occil.DiscreteExtra.cub` — accepted (derived)

Public specification: `SampLib.Cub.cub_distSpec`.

Source SHA-256: `3cea9623db2ce30039e9d8ad3e7e9f8b7bfb3150096d0aa041d061ffe3d3a4ff`.

The independent standard CUB law mixes one plus Binomial(m-1,1-ξ) with the uniform categories1..m. Named selector and component adapters isolate representation equalities from the simple two-branch CTE composition. Independent tests establish the bias orientation: selector1/uncertainty0 gives m, selector1/uncertainty1 gives1; selector0 is uniform1..m independently of uncertainty. Infinite credits and arbitrary framed clients are checked. This is explicitly a derived named composition.

## `Occil.WeightedVariants.flatChoice` — accepted (core)

Public specification: `SampLib.FlatChoice.flatChoice_distSpec`.

Source SHA-256: `951a35be657b4ad22aed1f6c16b4be307f0b8cbfbd68d8ef1f7728266bee1134`.

The deterministic table replicates each label exactly its weight. A table lookup theorem identifies a uniform position with the existing categorical rank partition; its canonical normalized law is WeightedChoice.law. A short raw syntax helper inserts only a locally closed tail continuation, keeping binder capture bookkeeping outside the main proof. The program logic transparently validates, expands, sums, draws a uniform rank and looks up the table. Tests check [0,2,0] and [1,0,2] tables, the unique positive label, infinite credit at zero-weight labels and generic framing.

## `Occil.WeightedVariants.lemireUniform` — accepted (core)

Public specification: `SampLib.LemireUniform.lemireUniform_distSpec`.

Source SHA-256: `2519ea9ff74a47d4b00ce4002877dc4bcdb8a1f61dadc28d8f476a10874cbf3c`.

Multiply-high reduction accepts exactly those source words whose low product is at least the Euclidean remainder. The accepted fibre for each label is an explicit interval of length floor(width/n), so finite fibrewise summation proves the exact uniform law. The remaining short mass pays doubled retry credit. Tests compute the n5/width8 accepted set {1,3,4,6,7}, show its quotient image is all five labels, check the boundary low product at source7, the complete arbitrary-ENNReal kernel, zero-bit singleton and framed clients.

## Supporting mathematics and deterministic code

BinomialBinary separates the canonical thinning/filling argument from expected unresolved population and the fixed amplification inequality. MultiplyHigh proves exact ceiling bounds, equal accepted interval fibres, fibrewise sums and accepted cardinality for arbitrary positive source widths. All continuation arithmetic remains in ENNReal.

IntegerChoose verifies the actual multiplicative binomial-coefficient loop for every natural n,k. The adjacent binomial identity proves each nonzero integer division exact; the main logic is finite remaining-step induction and the out-of-range guard. Independent clients require no UniformInt assumption, frame an arbitrary resource, and check zero, self, out-of-range and10choose3=120 cases. This deterministic helper is not counted as a sampler.

ListAccess and ListValues are direct closedness/freshness rewrites. Opening uses local closedness; closing requires explicit empty free variables. No arbitrary locally closed callback is incorrectly treated as free-variable-free.

Support hashes:

- `SampLib.Distributions.BinomialBinary`: `0ed415e550f31670e057fd1f3700ab45a911a4b7fd703f5a5ef7410c1ce26bde`.
- `SampLib.Distributions.MultiplyHigh`: `4c8ee729f5430948ff2c4201e53dafb72cbd1e8df67493b211ead9ebd1159b3f`.
- `SampLib.IntegerChoose`: `c02ddb26b9ac1bf2de1bb94542131d6e2ffd7f083f149835e026b0a6353249b4`.
- `SampLib.Syntax.ListAccess`: `1ff1681744767cb8c03cb1ccfc769d348046a3c7d2cd8e8ca636489577719cb1`.
- `SampLib.Syntax.ListValues`: `eb0b0faa8645aa926f0c1e50e03b48f9bcd0d30c7772db6f081d2b4f5a3ebdc6`.

## Validation

Independent gated module builds and working/immutable copied callers pass without warnings. CUB uses a local400000-heartbeat elaboration limit on its main theorem; the other included modules use default limits. Public specifications, new expectation lemmas, interval-fibre lemmas and IntegerChoose depend only on propext, Classical.choice and Quot.sound. All new Lean sources are at most100 columns with clean whitespace. Target laws are normalized and all specs admit arbitrary measurable ENNReal credits, including infinity.
