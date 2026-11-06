# Exact structured sampler review, batch 004

Reviewer: `/root/review_exact_b`. Accepted core interfaces:

- `SampLib.RefinedCoin.refinedCoin_distSpec`: SHA-256 `66fa542c7b155b691668036e5ce558baa69bdbb541e95cb304c39aff9b1587fd`. Arbitrarily tight dyadic probability enclosures, not necessarily nested and with no known convergence rate; both probability endpoints allowed. Bounds callbacks return the actual positive-level lower/upper numerators.
- `SampLib.RefinedCDFComparison.refinedCDFComparison_coinSpec`: SHA-256 `270c01fa4c0f49825902a2e10b02e8d2209dc1149d44296f18d07cf405eb9e9f`. Any initial owned cache, index and arbitrarily tight valid dyadic threshold enclosures. The returned comparison keeps the same latent uniform, refined prefix and arbitrary joint output/latent credits.
- `SampLib.IncompleteInformation.incompleteInformation_distSpec`: SHA-256 `ba31674fb28b24d44572d845c2eed6c389f93f1f15102ae83dcc962780aef974`. Any positive finite support size and monotone real-valued finite CDF reaching one, including irrational masses and zero-mass plateaus. Valid dyadic enclosure callbacks are required only at in-range indices.

## Expectation argument

One cached uniform underlies every refinement. A chosen finite horizon adds
one auxiliary credit exactly on its unresolved threshold interval. Its posterior
expectation costs at most interval width divided by the current cache-cell width.
Arbitrarily tight enclosures therefore make that cost arbitrarily small for every
initial cache, even without nested intervals or a convergence rate. Settled
branches retain the exact comparison and joint output/latent credit; unresolved
execution at the horizon contradicts possession of one whole error credit.
The positive-error rule removes the auxiliary budget. Nothing assumes finite
credits, and the argument applies at both probability endpoints.

The finite-CDF target is the independent first-reaching quantile pushforward of
one uniform. A separate theorem proves its cumulative mass is the supplied CDF.
Bisection maintains a posterior-almost-everywhere quantile bracket. Each comparison
uses the same cache and its learned threshold relation; either branch decreases
the integer bracket width. At a singleton bracket the quantile credit is exactly
the returned integer's credit. Plateaus need no positive atom assumption.

## Program logic and independent callers

The actual refinedCoin wrapper opens its certified source, allocates one bag,
invokes the shared loop and returns. Indexed comparison opens the actual source
and invokes the same loop. Incomplete sampling allocates its bag and symbolically
executes finite-width bisection. Source-opening plumbing is isolated in syntax
helpers; mathematical expectation and bracket facts are named separately. The
actual runtime implementation is unchanged and no desired concrete law is assumed.

The independent fixture supplies a real always-zero bound callback at Bernoulli
endpoint zero, also with infinite credit. It supplies a real indexed finite-CDF
bounds callback with three zero-mass positions and a certain final position;
the final dyadic numerator uses the verified integerPower program. Arbitrary
credit and an unrelated Iris resource survive both concrete samplers.

A generic joint cached-comparison caller preserves arbitrary G(bit,latent), cache
and frame. A second caller executes the actual threshold comparison twice on
that SAME cache. It derives equality of the two bits by transporting the first
almost-everywhere resolves fact to the final posterior, while retaining arbitrary
H(first,second,latent) continuation credit and the unrelated frame. This detects
the invalid interpretation as two independent marginal Bernoulli samples.

Each target was independently built; caller and exact-head/noncircular-signature
audits pass warning-free. All four printed public/law axioms checks use only
propext, Classical.choice and Quot.sound. ExactStructuredBatch004.log retains
commands and outputs. This immutable receipt binds local transitive sources,
independent caller and the current clutch06a7b3e dependency context.
