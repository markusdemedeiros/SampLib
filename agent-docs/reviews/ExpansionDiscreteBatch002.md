# Expansion discrete review: immutable batch 002

Reviewer: `/root/expand_review_discrete`. Five accepted named samplers, with
independent mathematical support reviews recorded below. Existing baseline and
batch 001 sources remain unchanged.

## `Occil.Weighted.uniformRational` — accepted (derived)

Public specification: `SampLib.UniformFormats.uniformRational_distSpec`.

Source SHA-256: `5d606df4aa59d17b72ea98196f259bee0cc2863212a1b906b0cdbd337720b54e`.

A derived representation of the canonical uniform integer law: the random numerator is uniform and the positive denominator is retained exactly. No continuous-uniform claim is made. The CTE proof composes the existing uniform primitive and constructs the pair. All receive arbitrary measurable ENNReal credits.

## `Occil.Weighted.uniformFixed` — accepted (derived)

Public specification: `SampLib.UniformFormats.uniformFixed_distSpec`.

Source SHA-256: `5d606df4aa59d17b72ea98196f259bee0cc2863212a1b906b0cdbd337720b54e`.

A derived fixed-grid uniform specification. The target is exactly the existing normalized finite-uniform law; symbolic execution delegates the random draw directly to its verified specification. All receive arbitrary measurable ENNReal credits.

## `Occil.Weighted.uniformDyadic` — accepted (derived)

Public specification: `SampLib.UniformFormats.uniformDyadic_distSpec`.

Source SHA-256: `5d606df4aa59d17b72ea98196f259bee0cc2863212a1b906b0cdbd337720b54e`.

A derived dyadic-grid representation. The denominator is verified by repeated squaring and the numerator by RandomBits. The zero-bit case is denominator one and numerator zero. The loop mathematics is inherited, while pair construction is explicit symbolic execution. All receive arbitrary measurable ENNReal credits.

## `Occil.DiscreteExtra.negativeHypergeometric` — accepted (core)

Public specification: `SampLib.NegativeHypergeometric.negativeHypergeometric_distSpec`.

Source SHA-256: `137305e0d93b64e2dcd58389c9831dc4460401746fd7af94dd9ecb47cf277a13`.

The independent target reads a uniformly permuted labelled urn until the requested marked draw, counting preceding unmarked entries. Partitioning the ordering by its first position gives the color recurrence. The CTE proof is finite two-counter induction; the new support continuation supplies positivity of the unmarked population on an actual failure. I suggested merging duplicate first-position expectation wrappers, and the author did so. Tests cover zero requests, no unmarked balls, a one-marked/one-unmarked population with expectation (F 0 + F 1)/2, arbitrary infinite credits, and framed caller resources. Requesting all marked balls does not consume any trailing unmarked balls. All receive arbitrary measurable ENNReal credits.

## `Occil.DiscreteExtra.himanshu` — accepted (derived)

Public specification: `SampLib.Himanshu.himanshu_distSpec`.

Source SHA-256: `34d0c9547d853253e5d2db18f5e88f68852a7280d498b2100a5a94fb99ddcebf`.

The callback builds one independent success block, whose verified Bernoulli bias is p^n; the existing geometric specification then gives the number of failed blocks. This is a derived composition and does not claim a rolling-window waiting-time law. The public proof needs no uniform-integer assumption. Tests cover block size one, the p=1 zero-failure endpoint, arbitrary infinite credits, and resource framing. All receive arbitrary measurable ENNReal credits.

## Supporting mathematics and program rules

- Repeated squaring proves ordinary integer powers for every integer base and
  natural exponent. Even/odd identities are outside symbolic execution; a
  reviewer-requested cleanup uses named positivity and division bounds in the
  program proof.
- `IsDistSpec.wp_supported` assigns infinite credit only outside an almost-sure
  measurable support set. Its integral is unchanged, and credit validity excludes
  the impossible returned branch. A generic caller proves preservation of an
  arbitrary unrelated resource together with the support fact.
- The independent Poisson tree mathematics counts parity-constrained complement
  subsets. Hockey-stick sums count stopping edges; forward/backward layer duality
  gives their atom masses; the even/odd exponential series yields the canonical
  Poisson(1) measure. Factorial cancellation is only by finite positive factors,
  and arbitrary continuation credits are never converted to real numbers.
  Tests check layers 2/3/4, odd and out-of-range zero masses, normalization,
  infinite credits, and the initial-state shift. This support acceptance does
  not count the Poisson sampler before its separate CTE review.

Support hashes:

- `SampLib.WeightedIntegerPower`: `4d98577633e04ebbf62d71c689bbc896d93cef55f88e7bb5b0e89fc9d1eee1f5`.
- `SampLib.SupportedSpec`: `560f5a523858a1b9a7df558927f70707c00ee9b302fb0091007726fe476adda2`.
- `SampLib.Distributions.PoissonTree`: `75fdf0831f7084696cf776bf1fb5c5aa38712bd78a9c9bb5ac0a2a9fb7690d8f`.
- `SampLib.Distributions.PoissonMeasure`: `e25cd2678db2066e41ab87bc5edcd464b08afac6458de8b8e29e6a55679dba80`.

## Validation

Independent gated module builds passed without warnings (4257 jobs). Both the
working and immutable copied caller artifacts compile without warnings. Public
specifications, central new mathematical lemmas, and the support rules inspected
in the caller file depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Source formatting and whitespace checks pass.
