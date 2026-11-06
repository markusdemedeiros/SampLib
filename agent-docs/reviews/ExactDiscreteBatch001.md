# Exact discrete sampler review, batch 001

Reviewer: `/root/review_exact_b`. Accepted
`SampLib.GeneralizedGeometric.generalizedGeometric_distSpec` in `SampLib/Samplers/GeneralizedGeometric.lean`,
SHA-256 `d54ba2f9b3123cd1b7494092cd323f899507c49e245cf3ebd09a69f2e6c9b4d7`. Classification: core.

## Law, normalization and termination

The independently defined stopping law places mass
`(product of earlier continuation probabilities) * (1-current probability)`
on each stopping depth, then shifts by one to match the source's positive index.
Finite stopped mass plus surviving mass telescopes to one. Vanishing survival
therefore normalizes the law, even when the waiting time has infinite expectation.
The one-step expectation identity retains arbitrary ENNReal continuation credits.

`AbsorbingChain.twp_finite` unfolds to a finite horizon, leaving only its survival
mass as extra credit. The depth-zero residual is one and contradicts the credit
invariant; the induction step is the ordinary stop/continue credit identity.
`twp_of_survival` removes that residual with the established liminf credit rule.
There is no unjustified uniform contraction or finite-mean hypothesis.

## Actual program and proof quality

The concrete callback theorem specifies source call `coin(n+1)` with probability
`p n`; it assumes no callback at zero. The CTE step calls that specification,
splits its Boolean result and either returns the positive stopping index or
uses the supplied recursive continuation. The public wrapper executes the actual
`Occil.DiscreteExtra.generalizedGeometric` term. Its hypotheses do not assume
correctness or termination of that concrete sampler.

Review was performed before and after polish. Broad measure-theory opening was
replaced by selective imports so the postcondition uses ordinary Iris notation.
The program proof remains straight-line symbolic execution; supporting mathematics
is separate. No runtime implementation or historical signed proof was changed.

## Independent checks

Targeted build, exact-head/noncircular public-spec audit and the independent
[caller fixture](ExactDiscreteBatch001Callers.lean) all passed warning-free.
The fixture exercises arbitrary indexed callbacks with arbitrary credit and an
unrelated Iris resource. A concrete always-false callback tests immediate stopping
at the first positive index without any uniform-integer assumption; the same
interface is instantiated with infinite credit.

The public theorem, finite-horizon/liminf support, stopping-law expectation and
independent test lemmas have only `propext`, `Classical.choice`, `Quot.sound` axioms.
The structural auditor reports `SPEC_OK` for the exact named source sampler.
Commands are retained in `ExactDiscreteBatch001.log`. The immutable receipt binds
all project-local dependencies, caller hash and the current `06a7b3e2` dependency
context. Domain: Any indexed fresh continuation-coin family, queried only at positive source indices, whose survival product from the first index tends to zero. No geometric rate, finite mean, or uniform-integer primitive assumption is required. The output is the positive first stopping index.
