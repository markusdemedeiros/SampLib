# Expansion discrete review: immutable batch 011

Reviewer: `/root/expand_review_discrete`. Three accepted core samplers.

## `Occil.uniformFromModulus` — accepted (core)

Public specification: `SampLib.UniformFromModulus.uniformFromModulus_distSpec`.

Source SHA-256: `c76650f505e2b92a3c80faa3bcfb7fa0582917fad1277a17b3a39e09f821d214`.

The canonical target is UniformInt.law n. Complete residue blocks conserve arbitrary output credit for small targets; independent high/low digits flatten to one uniform rectangle for large targets. Each retry retains at least half of its source range. The program proof separates the equal, smaller and larger target cases; strong induction supplies a relative closed low-digit specification, and both retry loops use one direct conservation bound and factor-two amplification. Independent tests check source5/target2 residue rejection, deliberately conservative source6/target2 cutoff, recursive widths2→7→4→2, source3/target8 rectangle, equal-modulus native draws, singleton infinite off-support credit and generic framing.

## `Occil.DiscreteExtra.negativeMultinomial` — accepted (core)

Public specification: `SampLib.NegativeMultinomial.negativeMultinomial_distSpec`.

Source SHA-256: `f1768bd9b2b6237a13614f611f988303273bab590029b8670fca792136be2915`.

The independent canonical law draws the negative-binomial total failure count, then allocates it with the standard multinomial PMF. Joint atoms factor at the returned count sum. The first-trial recurrence and categorical allocation identity yield one exact credit conservation lemma, including a remaining-success potential and fixed amplification1+p. Main CTE performs a supported categorical draw, decrements the remaining target or calls the pure indexed counter increment, then invokes its accumulator-universal induction hypothesis. Independent tests check a nonuniform joint count mass1/8, all-zero and absent failure categories, zero targets, infinite off-support credit, normalization and generic list-encoded resource framing.

## `Occil.DiscreteExtra.walleniusHypergeometric` — accepted (core)

Public specification: `SampLib.WalleniusHypergeometric.walleniusHypergeometric_distSpec`.

Source SHA-256: `128d4f9fca452622afd7bc8b251945ed8cc2dc5469e1ab28a9c28b19f6d3441f`.

The independent normalized color-word law exposes its explicit prefix product: remaining color count times odds, divided by current total weighted population. The Wallenius count law is its count pushforward; full-request support prevents overdraw. The two-color expectation is derived by identifying the categorical draw with the corresponding rational coin. Main CTE is finite draw-count induction, a supported selected-color coin, then the appropriate smaller urn call and optional marked increment. Independent unequal-odds tests use ones2/zeros1/odds3:1/n2: two marked draws have probability9/14, distinguishing Fisher3/5, while ordered mixed words have probabilities3/14 and1/7. Tests also cover zero draws without UniformInt, both empty-color boundaries, overdraw-zero mass, arbitrary infinite expectations and generic framing.

## Supporting mathematics and deterministic code

ModulusReduction proves complete residue-block and independent rectangular-digit expectation identities, with source/target bounds guaranteeing at least half acceptance. UniformSupport supplies the exact finite output support. NegativeMultinomial derives its categorical recurrence from the independent negative-binomial/multinomial mixture; MultinomialTrials transports one independent categorical trial, and NegativeBinomialStep exposes the canonical first-trial recurrence. Its fixed remaining-success potential gives exact conservation without subtracting arbitrary infinite credits. NatCounters was independently accepted in Batch010 and is pinned again for the actual indexed update.

Wallenius has the explicit prefix likelihood, exact remaining-population formula, normalized full-length word masses, no-overdraw support, count pushforward and equal-odds ordinary-urn characterization. Two-color coin equivalence and accumulator transport give the single program expectation identity. It claims no unproved integral PMF. BindFrom was already independently accepted support and only exposes an existing evaluation context.

Support hashes:

- `SampLib.Distributions.ModulusReduction`: `c6b00a495353f614e188be0b47cacc8ec38b799422297672fe1d3d66a25b4ae9`.
- `SampLib.Distributions.UniformRectangles`: `93f83aa1581c59fad91a2bac9644d49e864ff3da102a5316ccb193898195dbed`.
- `SampLib.Distributions.UniformSupport`: `019f54ee4d8709463cce0ae4deea00b67af419d72d9d790a3d56e213ccadce8e`.
- `SampLib.Distributions.NegativeMultinomial`: `450813ff722a721db5d0976355b1cc3d071738d15d2a72aa1a564b577277a57a`.
- `SampLib.Distributions.MultinomialTrials`: `2f076c8c9fe1f70d009d00277e74dea380cf1877d64d9d8fcc3a6382abf47f66`.
- `SampLib.Distributions.NegativeBinomialStep`: `b3f98d9da3153cc4abae38637db479c8a366aaf846919cbf6758008265027663`.
- `SampLib.Distributions.WeightedSupport`: `1bd3e47e01cc5641f8d5e23eb0ad8257da928e251a6fc4efaedf0f3dc7944fef`.
- `SampLib.NatCounters`: `041132bb64a0c8a53c2bdb929635f144b10cd1ae47ceeb2e1a6c3bfbdf65ab15`.
- `SampLib.Distributions.Wallenius`: `e45dca17c92da6efb2c5f404006994c4a8c0d5d722970d915b2bd2faa97b1e11`.
- `SampLib.ProofMode.BindFrom`: `c904ca958308f8d434bbaffa0128cbe5ab31d72ed884886946bcac98f973db54`.

## Validation

Independent gated module builds passed without warnings. Working and immutable copied clients compile without warnings. Public specs, central expectation lemmas, normalized likelihoods, mixture factorization and support lemmas depend only on propext, Classical.choice and Quot.sound. Source widths and whitespace pass. All targets are normalized with typed integer encoders, arbitrary measurable ENNReal credits and unrelated resources retained through calls.
