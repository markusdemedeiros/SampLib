# Exact factories batch 002

Reviewer: `/root/review_exact_a`.

The logarithmic wrapper supplies the verified rational coin callback to the existing
logarithmic factory. Its original lazy-uniform algorithm and full signed rational parameter
domain are preserved. Its bias is explicitly `log(1+a/b)`. The integer-power source contains
its own finite all-success loop; a direct induction executes that loop using the rational
coin specification. Its central expectation recurrence is the established IterateCoin
recurrence, without assuming the desired law of the concrete loop. Both entries are **derived**.
The CTE proofs contain no mathematical search or algebra beyond exact source normalization.

Independent callers preserve arbitrary Iris resources and exercise arbitrary credits, zero and
unit rational bases, the logarithmic endpoints, zeroth powers including `0^0`, and positive
powers at base zero with infinite credit on the null event. Coercion equalities identify all
boundary probabilities. No continuation credit is converted to a finite real number.

## Accepted sources

- `Occil.Constants.logOnePlusRational`: `SampLib.LogOnePlusRational.logOnePlusRational_distSpec`; source SHA256 `3e80398d70d33e48c74255529b03974ba1b48a2b57940b8bb6643b1d6caccfd6`.
- `Occil.Constants.rationalIntegerPower`: `SampLib.RationalIntegerPower.rationalIntegerPower_distSpec`; source SHA256 `86616d1fd219d7fb58e2b3c46b2bf725b24ea4a2e33df9873b194f69085d80e9`.

## Evidence

Independent caller: [ExactFactoriesBatch002Callers.lean](ExactFactoriesBatch002Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All implementation source files are unchanged from the frozen campaign baseline.
