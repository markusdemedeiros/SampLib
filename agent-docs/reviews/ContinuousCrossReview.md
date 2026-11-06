# Additional continuous-family review

Reviewer: `/root/prove_coin_combinators`, independently of the author and
`/root/review_structured`. Author files were not edited.

## Verdict

**Accepted:** Mixture, UniformMin, UniformMax, UniformSum. No correctness or
protocol blocker was found. This supplements `StructuredProofs.md`.

## Source assessment

- **Mixture:** the target is the normalized measure `p μ + (1-p) ν` on the
  original measurable output type. Both endpoint selectors are supported.
  The core proof calls the selector once and only the selected component.
- **UniformMin/UniformMax:** targets are pushforwards of two independent unit
  uniforms. The separate survival/CDF identities identify the expected order
  statistics. Strict comparison and equality branches return the correct
  mathematical min/max; the proof does not discard the diagonal as a null set.
- **UniformSum:** the target is the usual finite convolution family, initialized
  at `dirac 0`. Every natural count is covered. Symbolic execution draws the
  new uniform before the recursive rest, matching the implementation.
- All expectation proofs use nonnegative integrals/Tonelli and admit infinite
  credits. None assumes finite expectation, bounded credits, or an unproved
  distributional property of an implementation.
- Program proofs contain explicit binds, primitive/spec applications, branch
  refinements, and finite induction. Mathematical work remains outside them.

## Additional independent checks

`lake env lean /tmp/continuous-crossreview/Audit.lean` checks:

- Selector biases zero and one while the inactive component has infinite credit.
- All four min-survival/max-CDF endpoint identities.
- Infinite credit on the maximum's null singleton `{0}` integrates to zero.
- Constant-infinite continuation credits for min, max, and every uniform-sum count.
- The zero-summand point mass with infinite credit at zero and at an absent point.
- `UniformSum.law 1 = unifUnit`, by product-with-Dirac and map composition.
- A public-spec caller retaining an arbitrary Iris resource through uniform sum.
- Public-spec and order-statistic axiom audits: only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Nonblocking suggestions

1. In UniformSum's probability instance, `letI := ih` would express the purpose
   of `have := ih` more directly: the induction hypothesis supplies a local
   probability-measure instance.
2. If a later proof needs to simplify the sum target, the independently checked
   `law 1 = unifUnit` lemma is a useful API addition. There is no need to add it
   solely for this campaign or to expand the current core proof.

These suggestions do not affect acceptance or require a source change.

## Reviewed source hashes

- Mixture:
  `881a062192a581259a5050b170b12d033ed0eedb47f01189639b5eb20d72c420`.
- UniformMin:
  `dca6c6478f1b2ba07761d7ff593e5d9fe196c0f560629489f92ea83abbab1bba`.
- UniformMax:
  `48869b84a0d0afc034c14481aa37cde599d105eab02e1b4b7849025ed4602156`.
- UniformSum:
  `732c633030effeff70be03cd9baa0e593426cba26583267a814da06708b19462`.
