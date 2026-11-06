# Exact factories batch 004

Reviewer: `/root/review_exact_a`.

The actual factory passes a product coin with bias `p*cos(p)` and a sine coin to the
verified division factory. The source parameter order is respected: denominator `sin(p)`,
numerator `p*cos(p)`. The separate gap lemma identifies the supplied positive lower bound,
and the bias lemma identifies the result as `p/tan(p)`. Product expectation conservation and
the division theorem provide the mathematical argument. This is a **derived** sampler,
with exact symbolic CTE execution of the wrapper and both in-language callbacks.

The specification accepts arbitrary input callbacks through their proper IsDistSpec and never
assumes correctness of the concrete target sampler. Independent callers preserve an arbitrary
Iris frame, cover arbitrary credits, and instantiate the boundary input p=1 with a proved
positive gap witness e/f=1/5 and infinite success credit. The excluded p=0 endpoint is checked
to violate that witness. These tests distinguish the mathematical domain from runtime guards.

## Accepted sources

- `Occil.FactoryExtra.pOverTangent`: `SampLib.POverTangent.pOverTangent_distSpec`; source SHA256 `0899376099784974a5f10d4ae5dcaa8a52d3244a8a9dafc2f862f6d3d1483e31`.

## Evidence

Independent caller: [ExactFactoriesBatch004Callers.lean](ExactFactoriesBatch004Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All implementation source files are unchanged from the frozen campaign baseline.
