# Exact factories batch 011

Reviewer: `/root/review_exact_a`.

This is a core verification of the original reciprocal-hazard algorithm. Its survival coefficients are generalized binomial coefficients. The generalized binomial power series identifies the true exit mass as p^r; normalized first exits identify the complementary mass. A reciprocal accumulated-hazard bound makes survival vanish even at p=0, where the expected running time can be infinite. Finite unfolding carries residual survival credit, and the reviewed AbsorbingChain.twp_of_survival rule removes that residual by a liminf argument. No finite expected-time or uniform geometric-contraction assumption is imposed. Arbitrary continuation credits remain ENNReal throughout.

The source syntax opening is isolated in a checked structural syntax module and preserves arbitrary callback free variables. The program proof uses two coin specifications, explicit branches and its continuation; rational hazard domain facts and mathematical identities are outside that symbolic execution. Independent callers preserve arbitrary Iris resources and exercise the complete parameter domain, p=0 and p=1 with infinite credit on null events, and exponent1. Explicit bias identities and zero expected credit at the heavy-tail endpoint compile. The main theorem, program loop, expectation, survival, binomial mass identification and generic residual-credit theorem all have only standard transitive axioms.

## Accepted sources

- `Occil.fractionalPower`: `SampLib.FractionalPower.fractionalPower_distSpec`; source SHA256 `8699e04682cdd56f74ab695feb19402c6c4eec5a52b10779c0c5ed3272c7ef97`.

## Evidence

Independent caller: [ExactFactoriesBatch011Callers.lean](ExactFactoriesBatch011Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
