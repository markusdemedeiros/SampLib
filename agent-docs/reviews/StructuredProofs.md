# Independent review: structured sampler proofs

Reviewer: `review_structured`. Acceptance requires source/spec review, an
independent module build, an axiom audit, and a caller-level composition check.
An author's successful build alone is not an approval.

## Mixture

Status: **accepted**.

- Actual term: `Occil.mixture`, with an abstract selector and two abstract
  component samplers.
- Target: `p μ + (1-p) ν` on an arbitrary measurable output type with a common
  value encoding. The target is independent of operational execution.
- Domain: all `p ∈ [0,1]`; component laws are probability measures. No uniform-real
  primitive is assumed by the program theorem.
- Credit function: arbitrary measurable `α → ℝ≥0∞`, with no finiteness bound.
- Mathematics: one direct mixture-expectation lemma using measure linearity.
- Logic: symbolic execution, one selector-spec call, then the appropriate
  component spec. Matches source branch orientation exactly.
- Public spec: `SampLib.Mixture.mixture_distSpec`.
- Reviewed SHA256: `881a062192a581259a5050b170b12d033ed0eedb47f01189639b5eb20d72c420`.
- Independent build: `lake build SampLib.Samplers.Mixture` passed.
- Independent audit: `/tmp/review-structured/MixtureAudit.lean` compiled. It checks
  endpoint laws at `p=0,1`, a surrounding program bind retaining an arbitrary Iris
  resource, and both main/spec axiom lists. The only axioms are `propext`,
  `Classical.choice`, and `Quot.sound`.
- Caller detail: opaque `encode x` values require the explicit value rule
  `tglWp_value_of_toVal (e := (encode x).fst) (v := encode x)`; this is a tactic
  normalization detail, not a missing semantic hypothesis.
- Suggestions: none blocking from source review.

## Uniform minimum and maximum

Status: **accepted**.

- Actual terms: `Occil.uniformMin` and `Occil.uniformMax`.
- Targets: min/max pushforwards of the product of two independent unit-uniform
  measures. These are explicit mathematical order-statistic laws, not execution
  measures. The final files prove min survival `(1-t)^2` and max CDF `t^2` for
  every `t ∈ [0,1]`, identifying Beta(1,2) and Beta(2,1).
- Credits: arbitrary measurable extended-nonnegative functions.
- Mathematics: Tonelli and measurable pushforward give the single preservation
  lemma. Both measures are normalized by the product/map probability instances.
- Logic: two primitive uniform-credit redistributions followed by the source's
  strict comparison. Equality goes to the second sample in both actual terms;
  its value still equals the corresponding min/max.
- Suggestions: keep CDF identification concise and separate from symbolic
  execution; product-pushforward target is already semantically sufficient.
- Public spec: `SampLib.UniformMin.uniformMin_distSpec`; reviewed SHA256: `dca6c6478f1b2ba07761d7ff593e5d9fe196c0f560629489f92ea83abbab1bba`.
- Public spec: `SampLib.UniformMax.uniformMax_distSpec`; reviewed SHA256: `48869b84a0d0afc034c14481aa37cde599d105eab02e1b4b7849025ed4602156`.
- Independent validation: `lake build` for both modules passed; direct imports
  and framed callers in `/tmp/review-structured/OrderAudit.lean` compiled, as did
  all four endpoint identifications in `OrderEndpoints.lean`. Main/spec axiom
  lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Suggestions were resolved by concise separate survival/CDF lemmas. No blocking
  issue remains.

## Generic rejection

Status: **accepted**.

- Target: proposal measure restricted to the acceptance set and normalized by
  its positive mass. Arbitrary measurable output types are retained.
- Full positive acceptance, including mass one, is covered by the proposed
  amplification `1 + acceptanceMass` and an expectation inequality.
- The deterministic acceptance callback is specified for each encoded proposal;
  the proposal law is supplied through the reusable abstract sampler interface.
- Source review found no circular distribution law, hidden finite-credit
  restriction, or acceptance endpoint exclusion.
- Independent build and direct import passed. `/tmp/review-structured/RejectionAudit.lean`
  compiled with a concrete always-true acceptance callback at acceptance mass one
  and a generic framed caller retaining an arbitrary Iris resource.
- Main/spec/preservation axioms are only `propext`, `Classical.choice`, and
  `Quot.sound`. The caller unfolds `Rejection.credit` before passing it to `.wp`.
- No blocking suggestions remain.

- Public spec: `SampLib.Rejection.rejection_distSpec`.
- Reviewed SHA256: `a6f667c40bc8b6375ea16ac7067ab08608e84ea94e041efce7d75deaf378a055`.

## Uniform sum

Status: **accepted**.

- Public spec: `SampLib.UniformSum.uniformSum_distSpec`.
- Target: recursive convolution of independent unit-uniform measures, with
  `law 0 = dirac 0`; this is the full Irwin–Hall family for every natural count.
- Source draws the new uniform before recursive rest and adds the results. The
  proof follows exactly that order, with a measurable conditional expectation,
  one Tonelli/pushforward identity, and explicit finite induction.
- Arbitrary measurable ENNReal credits are retained; no finite-expectation bound.
- Independent module build and `/tmp/review-structured/SumAudit.lean` compiled,
  including the zero-summand target and a framed surrounding program.
- Main/spec axiom lists are standard only. No blocking suggestions.
- Reviewed SHA256:
  `732c633030effeff70be03cd9baa0e593426cba26583267a814da06708b19462`.

## Uniform list choice

Status: **accepted**.

- Public spec: `SampLib.Choice.choice_distSpec`.
- Domain: every nonempty finite list, arbitrary element type and value encoder.
  Mathematical output is a latent `Fin xs.length` position; duplicate entries
  remain separate positions. No measurable-space structure on the element type
  is assumed or needed.
- Target: uniform natural rank in `[0,n)` mapped to a finite index. The total map
  uses modulo outside the support and is exactly the identity on sampled ranks.
- Mathematics: one arithmetic-mean expectation lemma. Logic composes the actual
  list-length, uniform-integer, and in-range lookup specs, with explicit index
  bounds; the original sampler is unchanged.
- Support review: `listVal` matches the library nil/cons representation;
  `twp_length` and `twp_getAt` follow structural/finite-index induction and retain
  arbitrary encoded values. Support is not counted as an additional sampler.
- Independent build: `lake build SampLib.Samplers.Choice` passed.
- Independent `/tmp/review-structured/ChoiceAudit.lean` compiled: the list
  `[false,false,true]` gives true mass `1/3`, a generic surrounding bind preserves
  arbitrary Iris resources, and all four sampler/support axiom lists are standard.
  `ChoiceBoundary.lean` also compiles the singleton-list law.
- Reviewed proof SHA256: `b80822188b067db6777203c9e1e7bae41d78fe1da574267e6486e4da603e6ddc`.
- Reviewed support SHA256: `cfe9af21bfe11aeaf92b70f170c6026bfffc0d8aa589811c56776df1259ae6f0`. Support is still being extended for replacement;
  the existing reviewed helper declarations must remain unchanged or be rechecked.
- Suggestions: no blocking issue. The source explicitly explains latent positions,
  so the noninjective encoder for duplicate entries is not misrepresented.

## Probability-generating factory

Status: **accepted**.

- Public spec:
  `SampLib.ProbabilityGeneratingFactory.probabilityGeneratingFactory_distSpec`.
- Full domain: any natural-count probability law `ν`, any `p ∈ [0,1]`, and abstract
  verified count/coin callbacks. No moment assumption or bound on the count.
- Target: `ν.bind (IterateCoin.law p)`, explicitly the Bernoulli(`p^N`) mixture.
  It is normalized independently of execution. The single preservation lemma is
  measure-bind conditioning; count/output measurability is automatic from their
  discrete countable spaces. Arbitrary ENNReal credits are supported.
- Logic follows the actual code: obtain the natural count, discharge its negative
  guard, and invoke the verified finite iteration. Closure/freshness facts are
  local and do not replace the abstract callback specifications.
- Independent build: `lake build SampLib.Samplers.ProbabilityGeneratingFactory`
  passed. Both `/tmp/review-structured/PGFAudit.lean` and `PGFEndpoints.lean`
  compiled, checking a generic framed caller and the exact success mass
  `∫⁻ n, ofReal(p^n) ∂ν`, point-mass counts, `p=0` success mass `ν{0}`, and
  `p=1` full law `dirac true`. In particular, `0^0=1` is handled correctly.
- Main/spec axiom lists contain only the three standard Lean axioms.
- Reviewed SHA256: `5db3a3a5070f52cf6cb39fc52a4d58f57eac69aa9c1a99f4a2532baff7a4c66b`.
- No blocking suggestions. A public direct success-mass lemma is optional;
  the target mixture and its description already identify the PGF.

## Logistic factory

Status: **accepted**.

- Public spec: `SampLib.LogisticFactory.logisticFactory_distSpec`.
- Full actual-code domain: positive integer `x,y` and every `p ∈ [0,1]`.
  The final target bias is explicitly `x*p/(y+x*p)`. The actual rational selector
  is discharged by `RationalCoin.rationalCoin_distSpec`, not assumed correct.
- The internal selector `r=y/(x+y)` satisfies `0<r<1` exactly because `x,y>0`.
  Its extra bound does not narrow the real algorithm's public domain.
- The central preservation inequality states the two scalar fixed-point
  coefficients and a bounded amplified retry contribution. All credit algebra
  remains in ENNReal; only finite probability coefficients move through reals.
- The program proof is direct symbolic execution, selector/input-spec calls,
  and explicit error amplification. The integer/rational bridge is isolated
  from the logic and proves the stated source bias.
- Readability suggestion resolved: distribution, termination, conservation,
  integer-parameter and specification sections now organize the file. The shared
  real balance `q+D=1` is displayed before the coefficient transports. Program
  logic/public spec were unchanged by this polish.
- Independent module build and caller checks compile. Checks cover `p=0`, `p=1`,
  unit coefficients, null-success infinite credit at `p=0`, the complete
  expectation-inequality specialization with infinite credit, and an arbitrary
  Iris resource retained through a surrounding program bind.
- Main/spec/preservation axiom lists are standard only.
- Reviewed SHA256: `65fb8fe358fbf5ce6f5214418b0f6eb4cb31018fdb7bc576a491a7d2a481a616`.

## Sampling with replacement

Status: **accepted**.

- Public spec: `SampLib.SampleWithReplacement.sampleWithReplacement_distSpec`.
  It covers every nonempty input list and every natural draw count, including zero.
  `sampleWithReplacement_zero_distSpec` also covers an empty input list and needs
  no uniform-integer primitive assumption. Positive draws from an empty list are
  outside the algorithm's valid domain.
- The normalized law is the independent finite product of uniform list positions,
  encoded as the corresponding list entries. Equal entries retain their position
  multiplicity; independent replacement is explicit in the product measure.
- One Tonelli lemma gives the head/tail expectation identity for arbitrary
  measurable ENNReal credits. Finite induction composes the same callback spec at
  every draw, preserving independence without assuming injectivity of the encoder.
- The wrapper proof follows four pure steps and a call to the independent-repeat
  specification. The zero boundary executes the actual wrapper and returns nil.
  Deterministic encoding facts remain separate from the mathematical argument.
- Independent module build and source/import audit passed. Main, zero-boundary,
  and supporting repeat specs use only `propext`, `Classical.choice`, `Quot.sound`.
- Caller checks retain an arbitrary Iris resource through a surrounding bind,
  instantiate every sample size for a singleton alphabet, and exercise empty-list
  zero draws without a random-primitive assumption. For `[false,false,true]`, two
  independent draws are both true with probability `1/9`, checking duplicates and
  replacement together rather than only marginal probabilities.
- Reviewed SHA256: `430fa99ae768d75d13501fd70c5302775962a3b21cfadea3a76a2821121069fd`.
- No blocking suggestions remain.

## Shared list support

`SampLib/ListEncoding.lean` is accepted at SHA256
`cfe9af21bfe11aeaf92b70f170c6026bfffc0d8aa589811c56776df1259ae6f0`.
Its nil/cons representation is the actual library's sum/product representation.
Length and in-range lookup proofs are deterministic finite inductions, including
empty length and both zero/successor indices. Their standard-only axiom audits,
Choice callers with duplicate entries, and replacement callers exercise the
representation through actual object-language terms. No probabilistic premise or
measurable-space assumption on list element values is introduced by these helpers.

## Reproducible client evidence

`agent-docs/reviews/StructuredCallers.lean` consolidates the independently checked
caller, boundary, duplicate-position and infinity examples. Each original audit
is scoped separately to keep mathematical and Iris notation from interfering.
The main proof files are not cluttered with these regression examples.
