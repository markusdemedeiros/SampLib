# Next weighted and coin factory review

Reviewer: `/root/review_next_batch` (independent of the sampler authors).

## Cumulative categorical choice: accepted

Public specification: `SampLib.WeightedChoice.weightedChoice_distSpec`.
Reviewed direct-source SHA-256: `20483c16fdb6b45d60c13a5d6e9273a6c62257c1ea386c0a53f801ffc166e3f2`.

The specification covers arbitrary lists of natural weights with positive total,
encoded as nonnegative integer weights. Every nonnegative integer input list has
this representation. Zero weights, repeated weights and singleton categories are
included. The output is the natural category index encoded as a ProbLang integer.

The law is constructed by pushing a uniform rank through its category. This is
independently identified by `rank_partition`, `lintegral_law` and `law_singleton`:
each category has exactly weight/total mass, with zero mass outside the list.
The partition proof splits the rank sum into the first block and remaining blocks;
it never converts arbitrary ENNReal continuation credits to real numbers.

The CTE proof verifies the actual validator, sum, uniform draw and cumulative
selection. Deterministic list helper proofs are separate; the main proof follows
those calls with explicit binds and returns the rank's continuation credit.
There are no adequacy corollaries or hidden assumptions of correctness.

Independent `lake build SampLib.Samplers.WeightedChoice` and the persistent caller
suite passed without warnings. Callers preserve an arbitrary linear Iris resource.
Boundary checks include `[0,2,0]`, out-of-range positions, nontrivial mass 3/5 for
`[2,0,3]`, infinite credit on zero-probability positions, and infinite credit on a
positive-probability position. Transitive axioms of the spec and main mathematics
are only `propext`, `Classical.choice`, and `Quot.sound`.

Review suggestion addressed: expose `law_singleton`, making zero and out-of-range
weights explicit. Final pure-step formatting was reviewed after the cosmetic edit.

## Occil.bernsteinFactory: accepted

Public specification: `SampLib.BernsteinFactory.bernsteinFactory_distSpec`.
Reviewed direct-source SHA-256: `964f23561a3176ded195aa9b7c23ea4d1451e62753f6dad57c17bfae5131b6e6`.

All p∈[0,1] and nonempty lists of valid rational coefficients in [0,1]; includes degree zero and rational zero/one coefficients. Bias explicitly the Bernstein polynomial.

The target is the normalized binomial mixture of coefficient Bernoulli laws.
`success_probability` identifies it with the finite sum of rational coefficient
biases weighted by `choose n k * p^k * (1-p)^(n-k)`. The new mathematical binomial
bridge was authored by this reviewer and independently accepted by root; its
separate review and boundary/infinite-credit checks are recorded in
`NextBatchBinomialMath.md` and `NextBatchBinomialMathCallers.lean`.

The single expectation lemma conditions on the binomial count. Out-of-support
counts receive infinite credit; the count-support lemma proves these are null,
and credit validity discharges the impossible lookup branch. This retains arbitrary
continuation credits without strengthening the callback spec. The CTE proof then
performs list length, binomial draw, lookup and rational coin calls explicitly.

Independent persistent caller declarations check arbitrary linear framing,
degree zero with a half coefficient, degree one with coefficients zero and one
(reproducing every input bias), and infinite success credit on a zero coefficient.
The public specification and polynomial identity have only the standard three
axioms. Review request addressed: add the explicit polynomial identification;
a bind-mixture statement alone would not display the named function adequately.

## Occil.FactoryExtra.pLogInverse: accepted

Public specification: `SampLib.PLogInverse.pLogInverse_distSpec`.
Reviewed direct-source SHA-256: `efa14e4c414682db33ea37ddd89eb50dada53f6081d9dd9dc861a55a6a26b8ca`.

All terminating biases 0<p≤1; output Bernoulli(p log(1/p)), including deterministic false at p=1.

The geometric mixture is independently identified by the standard logarithmic
power series. The proof handles p=1 within the same series identity. It converts
only finite nonnegative probability coefficients through real numbers; arbitrary
ENNReal continuation credits remain ENNReal throughout the expectation lemma.
Equality on the success atom and normalization identify the whole Boolean law.

The CTE proof composes the verified geometric count and reciprocal rational coin,
with a separate deterministic zero-count branch. Review request addressed:
extract the zero-credit simplification so the program proof contains no expansion
of the Bernoulli PMF algebra. Independent caller declarations check arbitrary
linear framing, the p=1 deterministic endpoint, infinite credit on its impossible
success, and concrete composition with the verified integer fair coin.
Independent target build passed without warnings; specification and logarithmic
identity use only `propext`, `Classical.choice`, and `Quot.sound`.

## Integer-envelope categorical rejection: accepted

Public specification: `SampLib.WeightedRejection.weightedRejection_distSpec`.
Reviewed direct-source SHA-256: `9c8d0a10a70f75f9ece953045d03f14de76751290b0583a23f3fbefce524b915`.

The specification covers all nonnegative integer weight lists of positive total,
and every positive integer envelope bounding each weight. The output law is exactly
`WeightedChoice.law`, independent of the chosen envelope. Zero weights and the
all-accept case are included.

Write D = number of categories times envelope, S = total weight, and q=(D-S)/D.
Acceptance contributes (S/D) times the categorical continuation credit, while
rejection contributes q times the same credit plus amplification k=1+1/D of the
termination credit. The continuation terms therefore sum to the original credit;
q*k≤1 follows from the integer bound S≥1. This supplies the central expectation
inequality and handles q=0 without dividing by the retry probability. All
continuation arithmetic stays in ENNReal, including arbitrary infinite credits.

The CTE proof checks the actual guards and validator, then symbolically executes
length, uniform proposal, lookup, rational acceptance, and either return or retry.
The amplification induction separates termination and output credits. Closedness
normalization of the recursive term is explicitly isolated from the mathematical
argument. Review requests addressed: extract guard/domain facts, compress fixed
runs of deterministic reductions, and keep amplification independent of q>0.

Independent combined target build and the complete persistent caller suite passed
without warnings. The generic caller frames an arbitrary linear resource; concrete
callers cover an all-accept envelope and a list with zero weights and a larger
envelope. Shared categorical-law tests exercise zero/out-of-range probabilities
and both null-event and positive-event infinite credits. Printed axioms of the
public spec and central expectation lemma are only `propext`, `Classical.choice`,
and `Quot.sound`.

## Reproduction

```sh
lake build SampLib.Samplers.WeightedChoice SampLib.Samplers.WeightedRejection \
  SampLib.Samplers.BernsteinFactory SampLib.Samplers.PLogInverse
lake env lean agent-docs/reviews/NextBatchWeightedFactoriesCallers.lean
```

All four files are frozen at the hashes above. No runtime sampler was changed.
