# Exact structured sampler review, batch 007

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.HanHoshi.hanHoshi_distSpec`, SHA-256 `0ff63c38853a14afa12bfa4202e44e5cfba52824977e6235db392f5809831500`.

Domain: Every finite natural-weight vector of positive total, including zero weights, non-dyadic probabilities and certain rows. The output is the original-position integer label with the canonical categorical law. Arbitrary ENNReal output credit, including infinity, is supported; no finite runtime or continuation-moment premise is required.

## Mathematical argument

Continuous quantile inversion of the normalized cumulative weights is separately
identified with the canonical integer-ticket categorical law. A successful
cross-multiplied whole-cell scan proves that every point of the current half-open
dyadic cell has one output label. A failed scan exposes a cumulative boundary
STRICTLY inside that cell. Thus every point of an unresolved depth-N cell lies
within one cell width of one of finitely many boundaries.

The horizon credit adds one only on this finite union of open boundary bands.
Its initial expectation is at most desired output expectation plus twice the
number of boundaries times2^-N. Repetitions from zero weights are harmless.
That residual tends to zero independently of F, even when F is infinite. At an
unresolved selected horizon the posterior owns at least one contradictory credit;
settled cells retain the entire label credit. The positive-error rule removes
the auxiliary budget, without assuming a runtime expectation.

## Actual source and CTE

Review covered the real/integer CDF identification, cumulative cell classification,
rank and cross-product arithmetic, unresolved-boundary and horizon lemmas,
deterministic source scan, source-opening certificates and full fair-bit loop.
Validation is executed on the actual input. Each scan either returns its certified
original label or refines the SAME latent dyadic cell with one fresh fair bit.
The finite-horizon induction is ordinary symbolic execution of those two branches;
mathematical expectation and boundary facts are separate. No desired concrete
sampler law or termination premise is assumed. Runtime source is unchanged.

## Independent checks

Targeted build, exact-head/noncircular signature audit and caller pass warning-free.
The independent client retains arbitrary output F and an unrelated Iris frame,
including infinity, and calls the actual source on a sparse certain population.
For weights[1,0,2], pure source-scan fixtures show a coarse cell straddling1/3,
refined cells resolving on either side and the zero row being skipped. Additional
dyadic-boundary-contact fixtures certify the correct half-open cell convention.
All seven printed sampler/expectation/unresolved/CDF/band/client axiom checks use
only propext, Classical.choice and Quot.sound. ExactStructuredBatch007.log retains
commands and outputs. The immutable receipt binds all local support,
independent caller and clutch06a7b3e dependency context.
