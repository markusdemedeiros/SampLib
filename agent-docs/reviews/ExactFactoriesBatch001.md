# Exact factories batch 001

Reviewer: `/root/review_exact_a`.

All seven named terms perform one deterministic wrapper reduction and invoke the already
verified affine or reciprocal Machin-enclosure sampler. The mathematical output probabilities
are identified explicitly by the seven coercion lemmas. The expectation-preservation and
termination arguments are inherited from those enclosure theorems; no extra random primitive,
callback assumption, finite-credit restriction, or unproved concrete law is introduced.
All seven specifications are therefore classified **derived**. Their CTE fields are one
symbolic wrapper step, one named-bias normalization, and one verified specification call.

Independent callers instantiate every public theorem with arbitrary measurable Boolean credits
and an arbitrary framed Iris resource. Additional true-infinite and false-infinite continuation
cases exercise the extended-credit interface. All seven explicit real-bias equalities compile.
These fixed constants have no varying domain endpoints; their probability-domain certificates
are proved from the existing Machin interval and checked in the import closure.

## Accepted sources

- `Occil.Constants.piQuarter`: `SampLib.PiConstants.piQuarter_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.piTwelfth`: `SampLib.PiConstants.piTwelfth_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.piQuarterMinusHalf`: `SampLib.PiConstants.piQuarterMinusHalf_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.piMinusThreeOverFour`: `SampLib.PiConstants.piMinusThreeOverFour_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.piMinusThree`: `SampLib.PiConstants.piMinusThree_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.inversePi`: `SampLib.PiConstants.inversePi_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.
- `Occil.Constants.fourOverThreePi`: `SampLib.PiConstants.fourOverThreePi_distSpec`; source SHA256 `8582059fcd9c448a8ec460e938dfec7389a3ff971edc859c2c600fe7894bf4bc`.

## Evidence

Independent caller: [ExactFactoriesBatch001Callers.lean](ExactFactoriesBatch001Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All implementation source files are unchanged from the frozen campaign baseline.
