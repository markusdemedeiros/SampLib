# Deferred-uniform representation: independent review 001

Reviewer: `/root/review_exact_a`. Accepted as support, with no new sampler count.

The public certificates `SampLib.LatentUniform.representedOracleSpec` and
`SampLib.LatentUniform.newUniform_representedDistSpec` identify the actual returned
interval with a deterministic dyadic representation of the same owned uniform.
The existing constructor and observer execute the program; this extension strengthens
their postconditions without changing source or assuming the desired certificate.

For precision n, the interval rank is floor(x·2ⁿ), its denominator is 2ⁿ, and its
width is 2⁻ⁿ. The half-open posterior cell fixes that floor exactly. Refinement
preserves this almost-everywhere fact by absolute continuity, including when a later
read requests fewer digits. Floor inequalities give enclosure and shrinking width
for every real x; no endpoint or singular-null-event division is used.

The independently compiled caller reads the same physical handle through two equal
aliases at precisions 11→0→5. Its final posterior retains all three observations,
the owned cached state, arbitrary measurable latent ENNReal credit, and an arbitrary
Iris resource frame. A concrete continuation has infinite credit on x<1/2 and
value-dependent finite credit elsewhere. Boundary checks cover zero precision,
an exact dyadic boundary, and a negative nonboundary value. All five printed axiom
reports contain only propext, Classical.choice, and Quot.sound; compilation is clean.

Frozen source SHA256:

- `SampLib/LatentUniformRepresentation.lean`: `f6c48fe10bec5128cbd37739c6d2226ab3a8359eca2c6a38a2f6ea4766ebb66e`.

- `SampLib/Distributions/LatentReal/DyadicInterval.lean`: `b8a714d84c4e1c3a34a212cecbeb1bc8664bad7e8d5555460f272a9944efbbcd`.

Caller: [ExactUniformRepresentationReview001Callers.lean](ExactUniformRepresentationReview001Callers.lean), SHA256 `9ab2777370bf737a2eb9bb6cd66e158a319c25b3f819a35c5ced0a0687bc4de0`.

The adjacent JSON records the full dependency/context snapshot; the adjacent log
records the independent caller and axiom-check output.
