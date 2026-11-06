# Shared latent-uniform proofs

This document records the posterior invariant and the finite-horizon argument that the
bounds and factorial-series factories use. The bag foundation has an independent review in
[Factories Batch007](reviews/ExpansionFactoriesBatch007.json). For the current status of
each factory, see the [accepted suite](../SampLib/README.md).

A cached prefix `p` represents a single latent uniform value with posterior
`DyadicPosterior.law p`. Keep two things together: ownership of the original bag location,
and the credit `∫⁻ u, H u ∂DyadicPosterior.law p`, where `H` is the current conditional
output-credit kernel. Callback outcomes can change `H`. Preserve its one-step expectation
pointwise in the latent value. A comparison extends the cache and returns an almost-sure
fact about that same value. Later reads preserve earlier facts by absolute continuity
under prefix extension.

Two comparisons of the same bag are correlated. Apply `twp_uniformBagLess` with its
posterior credit. An unconditional Bernoulli specification for each comparison loses the
information that you need to compose them. Likewise, the conditional `sampleGeometricBag`
interface must keep the latent value in its credit kernel, even when the program observes
only its Boolean output.

For shrinking bounds, prove termination with a fixed global uncertainty interval. Given a
positive error allowance `δ`, choose a finite horizon `N` whose interval `B_N` has initial
uniform mass at most `δ`. Carry this kernel through every posterior refinement:

$$H(u)+\mathbf 1_{B_N}(u)$$

If execution reaches the unresolved horizon, its accumulated comparison facts imply that
`u ∈ B_N` almost surely. The indicator alone then supplies unit error credit, which
contradicts validity. Returns before the horizon deliver the output credit. You need no
bound on the conditional retry probability at individual cached states.

In the factorial-series factory, a surviving prefix contains only successful callback
trials. A failed grouped trial collapses the two bounds to the same partial sum and returns
without another factorial iteration. So the surviving horizon interval is deterministic.
Identify the output law separately, with an independent first-failure count and
alternating partial sums. Include the infinite count for a callback that always succeeds.
Preserve the conditional expectation kernel of that law pointwise through the program.
Unconditional interval widths do not describe the posterior at a cached state.

Keep all credits in ENNReal, including infinity. The initial expectation identity must
identify a normalized law. The termination indicator is auxiliary, and it must disappear
from the public `IsDistSpec` theorem.

The reusable interfaces are in [UniformBagLess](../SampLib/Latent/UniformBagLess.lean),
[DyadicPosterior](../SampLib/Common/Laws/DyadicPosterior.lean), and
[DyadicRefinement](../SampLib/Common/Laws/DyadicRefinement.lean).

## Keeping syntax transport out of symbolic execution

Prepare source equalities, openings, and closedness certificates before the continuous
TotalEris (CTE) argument. For large quotations, keep the named bodies through beta
reduction with the checked [BetaStep](../SampLib/Core/BetaStep.lean) rule. Its premises
are exactly a value argument and a locally closed lambda, so it adds no language
assumption. [PositiveSeries syntax](../SampLib/Constants/Syntax/PositiveSeries.lean) keeps
this bookkeeping apart from the probability argument. Walker's [opened-source
cache](../SampLib/Weighted/AliasSamples.lean) instead stores a kernel-checked normal form
without repeating the quotation.

Close templates before you insert arbitrary callback values. Local closedness does not
imply an empty set of named free variables. Keep such values as leaves with their existing
closedness proof. Reserve `ClosedExp` for constants that also have no named free
variables.

Two terms with identical `pl%` pretty-prints can have different ASTs. A common case is
`Exp.close` against an application that is already opened. Inspect the first structural
difference before you unfold everything or raise the heartbeat limit. Normalize closing,
internal-variable equality, and numeral conditionals in a pure transport lemma, and then
use one named rewrite in the program proof.

Give Boolean closedness computations explicit expressions and an explicit `rT`, because
their result type erases the language parameter. Likewise, instantiate the endpoints of a
pure-step rule before you discharge its side condition. An unresolved metavariable can
cause misleading timeouts or recursion-depth errors, even when the intended closedness
calculation is small.

## Measure-theory scopes in Iris proofs

Close broad `open MeasureTheory` scopes before the program-logic section. That namespace
activates the measure convolution notation `∗` at precedence 80, which collides with Iris
separation at precedence 35. The resulting errors can claim that the raw pure and
separation elaborators are unimplemented, even inside `iprop`. In the Iris section, open
only the names that you need, for example
`open MeasureTheory (Measure IsProbabilityMeasure lintegral_map)`. Changing existential
binders or importing `LocalBI` again does not resolve this notation collision.
