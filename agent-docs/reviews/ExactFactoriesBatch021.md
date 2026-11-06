# Exact factories batch 021

Reviewer: `/root/review_exact_a`.

This core proof verifies the actual rational-accumulator algorithm with one shared cached uniform. The first failed input callback freezes the partial sum; otherwise the remaining stopping threshold follows the geometric memoryless law, including its infinite endpoint. Conditional posterior credits preserve that threshold law at every step. An auxiliary horizon indicator costs only the deterministic enclosure width, which tends to zero. Surviving to the horizon makes its posterior credit at least1 and therefore contradicts valid error credit. This proves totality for all input biases, including p=1 with conditionally convergent coefficient series, without a finite expected-time bound. The Abel identity identifies the full coefficient-power series; absolute coefficient summability is never assumed.

The source state proof connects exact unreduced integer fractions and canonical arithmetic to the alternating lower and upper enclosures. Every comparison refines the same owned bag; no false independent-uniform approximation is used. Main CTE execution is horizon choice, a named initialization helper and finite decreasing-horizon execution. LC-certified source binder plumbing is isolated in the initialization and syntax helpers, preserving arbitrary callback free variables. Independent callers preserve arbitrary Iris resources and extended credits under the generic interface. An actual getter for harmonic coefficients1/(n+1) composes at p=1, explicitly exercising conditional convergence; p=0 has law1 with zero cost for infinite credit on false. The public exact-head/noncircular audit, full Abel and expectation/horizon axioms all pass with only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.alternatingSeries`: `SampLib.AlternatingSeries.alternatingSeries_distSpec`; source SHA256 `86a9e513361e75b56e8e31f98c1bc5b6d3b229dfcd09bae2dd1751b733ed67ba`.

## Evidence

Independent caller: [ExactFactoriesBatch021Callers.lean](ExactFactoriesBatch021Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
