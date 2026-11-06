# Exact factories batch 013

Reviewer: `/root/review_exact_a`.

The actual source constructs an exact Poisson count with mean3^(m+1), then independently rejects each event through the product callback (e/3)^m * exp(p)/3. Their product equals exp(m+p), so Poisson thinning yields exp(-exp(m+p)). The bias algebra is proved separately from symbolic execution. The source integer-power operation, Poisson draw, repeated constant coin and unknown-bias callback are all executed as written. This is a derived composition of reviewed Poisson, iteration, product and exponential-coin specifications, without numerical evaluation of the unknown probability.

Independent callers frame arbitrary Iris resources and arbitrary continuation credits, including infinity, under the full generic callback domain. They exercise m=0 with p=0 and p=1, identify the resulting exp(-1) and exp(-exp(1)) probabilities, and check the advertised general bias identity. The main theorem and CTE source proof print only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.expMinusExp`: `SampLib.ExpMinusExp.expMinusExp_distSpec`; source SHA256 `feee3e67858cd908218e4c3160988b236ad0cb3aba6239208214d757526f206f`.

## Evidence

Independent caller: [ExactFactoriesBatch013Callers.lean](ExactFactoriesBatch013Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
