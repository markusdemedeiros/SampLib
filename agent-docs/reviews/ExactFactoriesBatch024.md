# Exact factories batch 024

Reviewer: `/root/review_exact_a`.

This core proof verifies the actual joint linear-and-power factory. In the ordinary branch, logistic down/up motion preserves the requested power. When exponent times margin exceeds the source threshold3.55, exact rational-power selection cancels an amplification of the target bias and halves its margin. A capped reciprocal-margin budget remains positive for every initial exponent. Below threshold, its logistic drift pays a unit of work; above threshold, the selector survival bound below2/11 pays the increased budget and doubled ambient error credit. The budget proof derives that strict numeric bound from an exponential Taylor lower bound. This establishes total correctness without an artificial restriction on initial exponents.

A single arbitrary-ENNReal expectation separates power harmonicity from scalar budget drift, never converting continuation credit to a finite real. The program proof is exact callback execution, known guard branches and amplified induction. A reusable checked curried-beta rule and explicit source-opening facts preserve arbitrary callback free variables and isolate AST normalization. Independent callers frame arbitrary Iris resources and extended credits under the full scalar public interface. They cover zero coefficient with zeroth power0^0=1, positive powers at zero bias with null-event infinity, identity coefficient at p=1, unused invalid margins in the contracting branch, and expanding exact-margin n=1/n=8 cases on both source threshold branches. The latter output probability is checked as1/256. Public exact-head/noncircular audit and all printed program, expectation and drift axioms pass with only standard axioms.

## Accepted sources

- `Occil.FactoryExtra.linearPowerWalk`: `SampLib.LinearPowerWalk.linearPowerWalk_distSpec`; source SHA256 `4c338f54831b18908e0e831b41ef6841472e586457e641e4eacebbf20b07077b`.

## Evidence

Independent caller: [ExactFactoriesBatch024Callers.lean](ExactFactoriesBatch024Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
The shared Linear implementation file contains only the separately registered half-margin repair to linearLowProbability; the linearPowerWalk definition itself is unchanged from the frozen baseline.
