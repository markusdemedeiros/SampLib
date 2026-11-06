# Exact systematic inclusion review, batch 003

Reviewer: `/root/review_exact_b`. Accepted
`SampLib.InclusionSystematic.inclusionSystematic_distSpec` in `SampLib/Samplers/InclusionSystematic.lean`,
SHA-256 `cab6f93920df36d9a2f3befc630f1e825f471bd07a927a055b029e37b7b65982`. Classification: core.

## Mathematical argument and intended joint law

One uniform integer shift determines every selected category. The target measure
is the pushforward of that shared shift through cumulative-weight lattice
crossings, preserving dependence rather than replacing inclusions by independent
Bernoulli trials. `SystematicPPS.expectation` transports arbitrary ENNReal output
credit through the shift.

The identification is substantive: quotient increments telescope across the
population to prove the exact requested cardinality. Over one full shift period,
unit crossing increments telescope to one; summing a cell's integer width gives
its prescribed inclusion count. `inclusion_probability` therefore proves marginal
probability `count*weight/total`, including zero weights and capacity equality.
The finite label-membership argument excludes spurious repeated indices.

## Program-logic and polish passes

The CTE proof opens the actual source with two named beta steps, checks the source
guards, samples one uniform shift, and executes a deterministic scan. The scan
returns precisely the mathematical crossing list and spends no stochastic credit.
Guard/cast facts and certified source openings are separate from symbolic
execution; broad quotation normalization is absent from the main program proof.
The top-level distribution theorem is a small wrapper.

Review requested a zero-count endpoint outside the positive-total domain. The
supplementary `inclusionSystematic_zero_distSpec` now handles empty and zero-mass
populations without requiring a uniform-integer primitive, matching the source's
early return before weight validation. No runtime algorithm was changed.

## Independent checks

Independent targeted build, exact-head/noncircular structural audit and the
[caller fixture](ExactStructuredBatch003Callers.lean) passed warning-free.
Callers preserve arbitrary credit and an unrelated linear Iris resource, exercise
empty/all-zero zero-count inputs and positive sampling with zero-weight boundary
categories, and instantiate the boundary capacity case `[1,2,1]`, count two.

For that concrete case, the fixture checks the middle category's probability one,
an edge marginal one half and impossibility of selecting both edges together.
This checks the claimed joint dependence rather than only marginal frequencies.
It also invokes the exact sample-size theorem for every admissible shift.

The public main/zero specs and the sample-size/marginal theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. The structural auditor reports
`SPEC_OK` for the exact named source sampler. Commands are retained in
`ExactStructuredBatch003.log`. The immutable receipt snapshots the full local
source closure, caller hash and current `06a7b3e2` dependency context.

Domain: Any finite nonnegative integer weight list of positive total, natural count at most the population size, and count*weight<=total for each item. A supplementary zero-count spec covers every natural weight list, including empty/all-zero populations, without uniform-integer assumptions.
