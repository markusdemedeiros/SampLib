# Exact factories batch 027

Reviewer: `/root/review_exact_a`.

Minimum-complement is core; its minimum-half and six-mode piecewise wrappers are derived. A fair first-passage walk chooses a positive index. Its harmonic credit gives the smaller root, hence min(p,1-p). Ghost upper-barrier escape credit and a quadratic potential prove termination while preserving the actual unbounded walk; at the ghost barrier unit credit gives contradiction, and initial escape cost vanishes as the barrier grows. Infinite expected running time is allowed. At absorption the source binomial draw and its exact choose/power/rational acceptance coefficients realize that harmonic credit. Unimodality and the central Wallis bound certify every source coefficient; binomial cancellation gives(4*p*(1-p))^m/2. Root independently reviewed all seven pure mathematical modules, including endpoint and infinite-credit arguments, with durable evidence ExactMinimumComplementMathReview001.md.

The actual source opening and positive-index continuation are checked separately, so main CTE execution is open, walk, binomial stage. The stage executes the literal integer arithmetic and known rational acceptance spec; all normalization/domain setup is outside symbolic execution. The wrappers use exact fair means, conditional and negated coins, with full six-mode scalar formulas. Independent callers frame arbitrary Iris resources and arbitrary ENNReal credits for all three heads. A concrete verified fair-coin callback composes with the critical sampler; scalar checks cover0/1/fair input, minimum-half at1, deterministic piecewise endpoints and the common fair hinge. Null-event infinite credits have zero initial cost. Exact-head/noncircular audits and all printed program, harmonic/index, binomial expectation and bias axioms use only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.minimumComplement`: `SampLib.MinimumComplement.minimumComplement_distSpec`; source SHA256 `34a5866be039a4d81b1e928649f723aa7418009a53d5db935174421ceb3c82c4`.
- `Occil.FactoryExtra.minimumHalf`: `SampLib.MinimumComplement.minimumHalf_distSpec`; source SHA256 `74c8d80e729844b662820caf75d1de6d4fdc48619a666424886503c6beadaab2`.
- `Occil.FactoryExtra.threePointPiecewise`: `SampLib.MinimumComplement.threePointPiecewise_distSpec`; source SHA256 `2c574b4e0906d83459d293062837f8e23f008ce6c98a43e775a036ef8ad19637`.

## Evidence

Independent caller: [ExactFactoriesBatch027Callers.lean](ExactFactoriesBatch027Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
