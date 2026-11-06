# Shared latent-uniform proofs

This records the posterior invariant and finite-horizon argument being used for
the bounds and factorial-series factories. The bag foundation is independently
reviewed in [Factories Batch007](reviews/ExpansionFactoriesBatch007.json).
See the [accepted suite](../SampLib/README.md) for current factory status.

A cached prefix `p` represents a single latent uniform value with posterior
`DyadicPosterior.law p`. Keep ownership of the original bag location and the
credit `∫⁻ u, H u ∂DyadicPosterior.law p` together, where `H` is the current
conditional output-credit kernel. Callback outcomes may change `H`; preserve
its one-step expectation pointwise in the latent value. A comparison extends the
cache and returns an almost-sure fact about that same value. Later reads preserve
earlier facts by absolute continuity under prefix extension.

Two comparisons of the same bag are correlated. Apply `twp_uniformBagLess`
with its posterior credit; an unconditional Bernoulli specification for each
comparison would lose the information needed to compose them. Similarly, the
conditional `sampleGeometricBag` interface must retain the latent value in its
credit kernel, even when its Boolean output is all the program observes.

For shrinking bounds, use a fixed global uncertainty interval to prove
termination. Given positive error allowance `δ`, choose a finite horizon `N`
whose interval `B_N` has initial uniform mass at most `δ`. Carry the kernel

$$H(u)+\mathbf 1_{B_N}(u)$$

through every posterior refinement. If execution reaches the unresolved horizon,
its accumulated comparison facts imply almost surely that `u ∈ B_N`. The
indicator alone then supplies unit error credit, contradicting validity. Returns
before the horizon deliver the output credit. No bound on the conditional retry
probability at individual cached states is needed.

For the factorial-series factory, a surviving prefix contains only successful
callback trials. A failed grouped trial collapses the two bounds to the same
partial sum and returns without another factorial iteration. Thus the surviving
horizon interval is deterministic. Identify the output law separately using an independent
first-failure count and alternating partial sums, including the infinite count
when the callback always succeeds. Preserve its conditional expectation kernel
pointwise through the program; unconditional interval widths do not describe the
posterior at a cached state.

Keep all credits in ENNReal, including infinity. The initial expectation identity
must identify a normalized law; the termination indicator is auxiliary and must
disappear from the public `IsDistSpec` theorem.

The reusable interfaces are in [UniformBagLess](../SampLib/Latent/UniformBagLess.lean),
[DyadicPosterior](../SampLib/Common/Laws/DyadicPosterior.lean), and
[DyadicRefinement](../SampLib/Common/Laws/DyadicRefinement.lean).

## Keeping syntax transport out of symbolic execution

Prepare source equalities, openings and closedness certificates before the CTE
argument. For large quotations, retain named bodies through beta reduction with
the checked [BetaStep](../SampLib/Core/BetaStep.lean) rule. Its premises are exactly a
value argument and a locally closed lambda; it adds no language assumption.
[PositiveSeries syntax](../SampLib/Constants/Syntax/PositiveSeries.lean) separates this
bookkeeping from the probability argument. Walker's
[opened-source cache](../SampLib/Weighted/AliasSamples.lean) instead stores a
kernel-checked normal form without repeating the quotation.

Close templates before inserting arbitrary callback values. Local closedness
does not imply an empty set of named free variables. Preserve such values as
leaves using their existing closedness proof; reserve `ClosedExp` for constants
that also have no named free variables.

Identical `pl%` pretty-prints can hide different ASTs, particularly `Exp.close`
versus an already opened application. Inspect the first structural difference
before unfolding everything or increasing heartbeats. Normalize closing,
internal-variable equality and numeral conditionals in a pure transport lemma,
then use one named rewrite in the program proof.

Supply explicit expressions and `rT` to Boolean closedness computations: their
result type erases the language parameter. Likewise, instantiate a pure-step
rule's endpoints before discharging its sidecondition. An unresolved
metavariable can cause misleading timeouts or recursion-depth errors even when
the intended closedness calculation is small.

## Measure-theory scopes in Iris proofs

Close broad `open MeasureTheory` scopes before the program-logic section. That
namespace activates measure convolution notation `∗` at precedence 80, which
collides with Iris separation at precedence 35. The resulting errors can claim
that the raw pure/separation elaborators are unimplemented, even inside `iprop`.
Use selective openings such as `open MeasureTheory (Measure IsProbabilityMeasure
lintegral_map)` in the Iris section. Changing existential binders or importing
`LocalBI` again does not resolve this notation collision.
