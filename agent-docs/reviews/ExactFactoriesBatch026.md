# Exact factories batch 026

Reviewer: `/root/review_exact_a`.

The error-function construction is core: its actual nested chain draws the maximum of two uniforms, whose CDF is x^2. The FTC gives parity-flip mass1-exp(-x^2); arbitrary terminal credits therefore propagate through the decreasing-chain recurrence. A strict cap is selected from the actual outer uniform proposal in(0,1), providing amplification for every recursive chain call without falsely claiming a uniform contraction at the singular cap1. Even parity accepts the proposal with weight exp(-t^2), and the independent retry-credit argument identifies the normalized Gaussian integral, equivalently the classical erf ratio.

The integer-gamma construction is derived. Its actual maximum order statistic of m uniforms proposes density m*t^(m-1). The established decreasingTrial parity has acceptance exp(-t), and the verified threshold-rejection mixture cancels the factor m, giving the ordinary lower incomplete-gamma integral ratio. The public natural shape is positive; the internal exponent is exactly m-1. Mathematical expectation preservation is separate from the obvious source stepping, and no concrete target-correctness premise or finite continuation bound is assumed.

Independent callers retain arbitrary Iris resources and arbitrary ENNReal credits through both public actual source heads, every positive shape and both threshold endpoints. They prove the classical integral identities, nonzero Gaussian/gamma denominators from positive acceptance mass, endpoint scalar laws0 and1, and zero expected cost for infinite credit on impossible endpoint outcomes. The smallest shape m=1 is instantiated. Both exact-head/noncircular-premise audits and all printed main, chain, expectation and integral identities use only standard axioms.

## Accepted sources

- `Occil.Constants.erfRatio`: `SampLib.ErfRatio.erfRatio_distSpec`; source SHA256 `a82b823337089efeee2232f40b27df860b68797403ebe1cb8fd15915e70b0a6f`.
- `Occil.Constants.lowerGammaIntegerRatio`: `SampLib.LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec`; source SHA256 `a913c3da261cb37db7b3fbb8b5941c29a138acee79d21392dfc48d76714a66c6`.

## Evidence

Independent caller: [ExactFactoriesBatch026Callers.lean](ExactFactoriesBatch026Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
