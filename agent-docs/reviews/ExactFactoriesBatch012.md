# Exact factories batch 012

Reviewer: `/root/review_exact_a`.

This core proof treats the two return outcomes as marked exit masses of an indexed absorbing chain. The countable output measure is normalized by vanishing survival, and its false atom is exactly the coefficient PGF evaluated at1-p. Normalized hazard coefficient mass gives absorption for every input bias, including p=0; arbitrary zero hazards and finite-support schemes are allowed. No finite expected-time bound or uniform contraction is imposed. The central one-step expectation identity retains all credits in ENNReal, and the shared finite-residual/liminf rule establishes total correctness.

The CTE proof executes the actual input coin, deterministic hazard callback, rational coin and recursive continuation in order. Rational domain/specification setup is separated from that execution. Structural loop extraction finalizes binders before inserting arbitrary callback values, avoiding free-variable capture. Independent callers frame an arbitrary Iris resource under the complete generic domain, instantiate a zero first hazard followed by a unit hazard, and prove zero expected credit for infinite credit on the impossible outcome at both p endpoints. The public sampler and normalization/PGF theorems print only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.powerSeriesHazards`: `SampLib.PowerSeriesHazards.powerSeriesHazards_distSpec`; source SHA256 `cf199bf7a5503897a87547f41be3ee53ed8770e8905664cdc961027890efd276`.

## Evidence

Independent caller: [ExactFactoriesBatch012Callers.lean](ExactFactoriesBatch012Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
