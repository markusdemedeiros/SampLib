# Independent shared latent comparison support review

Reviewer: `/root/review_exact_b`. Support only; no additional sampler counted.
Public interfaces reviewed: SampLib.LatentReal.Less.twp_less and less_eventSpec.

- `SampLib/PSRNLess.lean`: `a87fe167b29d3ae98b7519f6f38b3cedf96d7eee119f00651fd28ab6fdae6300`.
- `SampLib/Syntax/PSRNLess.lean`: `fc5c9db941356866a2a9b5a6e8e8a3bacbac559c10edfe1864529d3686cba6c3`.
- `SampLib/Distributions/LatentReal/LessKernel.lean`: `c3281a2fa0be24d4f30560c803d13c65af472169d926e439a3f05d478a43e944`.
- `SampLib/Distributions/LatentReal/ComparisonUncertainty.lean`: `06676ddea2611973be43e958e589b1d0b107534a975ce5fc697d86e33b24a41f`.
- `SampLib/LatentMeasuredError.lean`: `ef3597d278dbb822b5231e26abf90755949202178e7a12fa1887dfcb6af844b0`.

A single fixed precision horizon pays one auxiliary credit only on the
unresolved joint uncertainty band. Measurable errors and almost-everywhere
distinct values make this band's original-posterior mass vanish by dominated
convergence. No nested schedule, conditional uniform retry bound, independence,
or finite continuation expectation is used. An unresolved execution at that
horizon contradicts ownership of one whole credit. The positive-error rule
removes the auxiliary budget.

Actual left and right source reads consume one shared P sequentially. Absolute
continuity transports the first enclosure to the final posterior. The two exact
cross-multiplied endpoint tests resolve strict order or its complement; state-local
almost-everywhere distinctness is explicit, retained under later refinements and
packaged in the reusable event callback. Equal values are not promised termination.

The independent targeted build and caller pass warning-free in
ExactSharedComparison001.log. The generic actual-source caller preserves arbitrary
joint G(bit,world) and unrelated Iris frame. A concrete dependent/aliased example
compares U with negate(U), reading ONE uniform source twice, including infinity.
Their exceptional equality at zero is removed by absolute continuity from the
nonatomic unit law, not a pointwise false premise. A separate zero-input-credit
calculation requests infinity on the comparison's null true branch and obtains
zero. Public logic, expectation and client axiom checks use only propext,
Classical.choice and Quot.sound. The immutable concrete-sampler receipts that
later use this support must snapshot its full transitive closure.
