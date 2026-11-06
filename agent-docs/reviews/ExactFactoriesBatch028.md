# Exact factories batch 028

Reviewer: `/root/review_exact_a`.

This core proof verifies the actual geometric-jump linear factory. A successful input flip decrements the power state; failure adds an independent geometric jump. Their division-free generating-function relation preserves target power even at p=0. In a fixed stage, a positive explicit escape probability bounds ordinary continuation, funding inner amplification1+escape. At the boundary, exact power selection cancels probability amplification while passing doubled outer slack with selector probability<=1/2. Root independently reviewed all five pure mathematical modules, with durable endpoint/two-slack evidence ExactLinear2014MathReview001.md. Arbitrary continuation credit remains ENNReal throughout.

The source-specific CTE proof has two nested error inductions. The outer induction is packaged as a linear continuation resource, framed through the entire inner stage induction, passed unchanged on ordinary retries and consumed exactly once at an accepted boundary. Returning and rejecting branches discard it lawfully. Inner slack is discharged separately before the outer continuation is invoked; no outer induction/resource is duplicated. Checked source-opening and curried-beta helpers retain arbitrary callback free variables. Main source execution covers both contracting and expanding branches and both explicit644/1000 margin-clamp choices.

Independent callers preserve arbitrary Iris resources and extended credits on the complete scalar domain. They instantiate exact low-margin and high-margin boundaries with target probabilities1/2 and1/4, zero bias, zero coefficient, and identity probability1; unused invalid margins remain allowed in the contracting case. Infinite credit on impossible outputs is checked to cost zero. Public exact-head/noncircular auditing and all printed program, nested-loop, central expectation and jump/escape axioms use only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.linear2014`: `SampLib.Linear2014.linear2014_distSpec`; source SHA256 `965f34a0ad1ba6d7ca84d81db01b415265b22aa2f7c37384f2b6cd9466953e55`.

## Evidence

Independent caller: [ExactFactoriesBatch028Callers.lean](ExactFactoriesBatch028Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
The shared Linear implementation file contains only the separately registered half-margin repair to linearLowProbability; the reviewed sampler definition itself is unchanged from the frozen baseline.
