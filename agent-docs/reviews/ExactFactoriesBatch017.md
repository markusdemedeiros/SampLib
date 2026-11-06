# Exact factories batch 017

Reviewer: `/root/review_exact_a`.

Two-coin power is core: the source first samples the base callback, then the exponent callback and a rational1/(n+1) gate. Its first-exit hazard is q/(n+1), so the reviewed binomial survival and exact exit-mass argument identifies p^q. The residual-credit liminf rule proves termination on the whole p>0 or q>0 domain, including the zero-base heavy-tail endpoint. The zero-zero pair has no exit and is honestly excluded. The two rational-power variants are derived: integer iteration and residual fractional power multiply by the quotient/remainder rpow identity, using nonnegative-base addition to preserve p=0 and exponent0. Both distinct source heads and their actual evaluation orders are executed.

Independent public callers preserve arbitrary Iris resources, permit arbitrary free-variable input callbacks, and use arbitrary ENNReal continuation credits. They exercise positive unknown exponents at base0, zero exponent at positive unknown base, and prove null-event infinite credit costs zero in both cases. Both rational-power source variants are framed; zero, integral and nonintegral rational exponents are instantiated, including0^0=1 and positive powers at base0 with infinite credit on the impossible success. Probability identities at p=0 and p=1 compile. Every printed specification and expectation uses only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.twoCoinPower`: `SampLib.TwoCoinPower.twoCoinPower_distSpec`; source SHA256 `867929217cc4ce92e6855b7f0a439af3470a066d5380d841424b235551f8cf9d`.
- `Occil.FactoryExtra.rationalPower`: `SampLib.RationalPower.rationalPower_distSpec`; source SHA256 `6952c1001f194403d6e8e0eb80021456a31e2970531e521eaf55812d7c0c0c33`.
- `Occil.DiscreteExtra.rationalPowerCoin`: `SampLib.RationalPower.rationalPowerCoin_distSpec`; source SHA256 `6952c1001f194403d6e8e0eb80021456a31e2970531e521eaf55812d7c0c0c33`.

## Evidence

Independent caller: [ExactFactoriesBatch017Callers.lean](ExactFactoriesBatch017Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
