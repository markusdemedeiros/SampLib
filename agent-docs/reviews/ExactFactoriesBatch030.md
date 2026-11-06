# Exact factories batch 030

Reviewer: `/root/review_exact_a`.

The core polynomial proof verifies the actual automatic degree-elevation search and exact rational coefficient conversion. The conversion uses falling-factorial/binomial coefficients, not point evaluation at the Bernstein grid. Its algebraic admissible-degree witness is finite termination data, with no assumed program correctness or desired-head specification. Every accepted degree represents the same polynomial by the Bernstein factorial-moment identity. Uniform convergence of the exact converted coefficients and compact strict-range margins separately prove that every polynomial strictly between zero and one on the closed unit interval admits such a degree. Root independently reviewed both pure mathematical modules in ExactPolynomialBernsteinMathReview001.md.

Deterministic source helpers verify signed and unreduced rational lookup, choose, multiply, add, table collection and admissibility testing. Named checked raw-code and cached closure transports isolate all source normalization. The recursive CTE search simply collects and tests the current table, then either invokes the reviewed Bernstein engine or advances the degree under a decreasing finite bound. Callback free variables are preserved without an extra closure assumption. The derived rational wrapper executes the actual Bernoulli race between two verified polynomial callbacks; only their combined value at the input bias must be positive.

Independent callers preserve arbitrary Iris resources and ENNReal credits on both full public interfaces. A signed unreduced input represents p^2-p+3/10: its degree2, degree3 and degree4 conversions have negative coefficients, whereas degree5 is admissible. The fixture proves these exact failures and success, composes the strict-range corollary, checks p=0 and p=1, and exercises polynomial zero and deterministic rational boundary laws with null-event infinite credit. Both exact-source-head/noncircular-premise audits and all seven printed program/analytic axiom reports pass with only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.polynomial`: `SampLib.PolynomialFactory.polynomial_distSpec`; source SHA256 `3abff1fed534147509c1902d452d69c774947346358d9dfea6ae43bd43ca6f4c`.
- `Occil.FactoryExtra.rationalFunction`: `SampLib.PolynomialFactory.rationalFunction_distSpec`; source SHA256 `ce5e8ec0ebd8349f972107d828f4fc32f6d7fc3779b976afe39ec6520c9a0f77`.

## Evidence

Independent caller: [ExactFactoriesBatch030Callers.lean](ExactFactoriesBatch030Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
