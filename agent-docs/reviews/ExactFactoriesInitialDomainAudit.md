# Exact factories: initial domain and interface audit

Reviewer: `/root/review_exact_a`. Context: installed `clutch-lean` `06a7b3e2`.
This is an initial source audit, not an acceptance receipt. No proof is accepted here.

The review covers the actual existing `pl%` terms in Bernoulli Powers, Series,
Trigonometric, Linear, Exponential, and Constants Engines, Exponential, Pi and Special.
The acceptance standard is [VerifyingSamplers.md](../VerifyingSamplers.md).

## Required obligations

- `fractionalPower` and `twoCoinPower` require nonuniform termination arguments.
  In particular, zero base probability is a valid nontrivial endpoint; a fixed
  retry contraction available only at positive base probability cannot discharge it.
  For `twoCoinPower`, the pair of zero probabilities diverges and must be excluded.
- `alternatingSeries` retains the same lazy uniform across all partial sums.
  The alternating coefficient conditions control its brackets; separate marginal
  comparison laws do not establish the algorithm's law under adaptive reuse.
- `envelopeFactoryDegrees` additionally needs Bernstein degree-elevation consistency
  and exact hypergeometric conditional averaging. Pointwise upper/lower bounds
  and convergence alone do not suffice. The source's rational normalization must
  be proved as executed, including every nonzero denominator used after survival.
- `minimumComplement` combines a fair first-passage walk with a binomial mixture.
  The fair walk has no uniform geometric termination bound; the Catalan mixture
  and its normalization must be established, including all endpoint biases.
- `polynomial` searches unboundedly for admissible Bernstein coefficients.
  A termination theorem must identify a sufficient mathematical domain, rather
  than assuming the concrete source program terminates or already has its target law.
- `alternatingPermutation` uses one geometric count and an alternating-order
  uniform event. Its Euler-number volume identity and convergence are substantive
  mathematical obligations. A numeric check of permutation frequencies is insufficient.
- `arctanFactory`, logarithmic-ratio factories and `zetaRelated` reuse latent bags.
  Callback specs must preserve the joint owned latent state across calls. Fresh
  unconditional marginal coin laws would assert an incorrect independence property.
- `erfRatio` uses maxima of two uniforms in a decreasing chain; its parity kernel
  is governed by the square of the initial comparison value. The gamma-ratio
  construction instead starts from a maximum order statistic and ordinary chain.
- Named affine/reciprocal pi and scaled-e wrappers inherit their substantive
  expectation and termination proofs. They should be recorded as derived entries,
  without manufacturing a second expectation argument or a new algorithm count.

## Known false unrestricted statements

`linearLowProbability` does not satisfy its advertised margin contract. The
inner call demands `(a/b)p <= 2(m/n)^2`, while the advertised domain promises only
`(a/b)p <= m/n`. The existing exact-rational certificate also establishes a strict
output-probability error at `(a,b,m,n,p)=(2,1,1,4,1/8)`. See the
[earlier domain findings](ExpansionDomainFindings.md#low-probability-linear-wrapper).
A corrected source margin must be handled as an explicit repair, with changed
source/review snapshots; restricting the theorem silently is unacceptable.

`rationalContinuedFraction` has guard-valid positive coefficient sequences whose
first descent diverges with positive probability. Its total specification needs
an explicit mathematically justified termination domain. The documented example
and union bound are in the
[continued-fraction finding](ExpansionDomainFindings.md#unrestricted-positive-rational-continued-fractions).

## Independent acceptance pass

Each acceptance will record the exact public theorem and source hash, normalized
output law, domain, mathematical preservation argument, simple CTE structure,
standard-only transitive axioms, and independently compiled arbitrary-resource
continuation callers. The receipts will pin the new dependency context and full
project-local source closure. Historical receipts remain unchanged.
