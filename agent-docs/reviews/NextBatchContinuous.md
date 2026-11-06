# Independent review: continuous next batch

Reviewer: `review_next_batch/review_continuous_next`. All three concrete public specifications are accepted.

## Mathematical and program review

- Exponential targets mathlib `expMeasure 1`, not a recursively defined output law. The positive half-line is partitioned into disjoint half-open integer strips, translated to the unit interval, and identified with the exponential density. Null endpoints justify changing `Ico` to `Icc`. The decreasing-chain parity recurrence selects accepted fractional parts; retry mass `exp(-1)` times amplification `exp(1)` is exactly one. Both expected credits and termination slack are tracked explicitly.
- The decreasing-chain term is definitionally equal to the upstream verified term (`implementation_eq` is proved by `rfl`). Its upstream proof covers starts at both zero and one and arbitrary ENNReal credits; reuse avoids copying the factorial/parity infrastructure. It is supporting infrastructure, not another counted sampler.
- Laplace uses the standard probabilistic construction: a unit-exponential magnitude and an independent fair sign. Its normalized product-pushforward law has an explicit reflection identity and reflection-invariant measure. Fubini supplies the single expectation-preservation lemma; the CTE proof composes verified exponential and fair-coin specifications.
- Erlang uses the standard probabilistic construction as a sum of independent unit exponentials. The public theorem covers every positive natural shape. The internal predecessor index is made explicit (`law 0` is one exponential), and the expectation lemma matches ProbLang evaluation order: the recursive right summand executes before the left exponential call.

## Suggestions and resolutions

- Requested meaningful law characterization beyond an algorithm-shaped name. Exponential uses the existing standard measure; Laplace adds reflection and Erlang exposes the shape-one identity. The latter two standard independent-variable constructions match the existing finite-convolution suite convention; a separate gamma-density identification is not claimed.
- Requested removal of repeated deterministic-step lines: Erlang now uses `iterate 5 twp_pure` while retaining explicit logical steps.
- Suggested reuse of exponential freshness/open/close lemmas instead of duplicated local helpers; both dependent proofs now reuse them.
- Requested removing inline parity arithmetic from exponential symbolic execution; the final odd branch rewrites the known remainder directly.
- Found a module-system warning from a redundant direct mathlib import; the import was removed and the final independent build is warning-free.

## Independent validation

Commands run successfully on the final sources:

```sh
lake build SampLib.Samplers.Exponential SampLib.Samplers.Laplace SampLib.Samplers.Erlang
lake env lean agent-docs/reviews/NextBatchContinuousCallers.lean
```

The caller file frames an arbitrary Iris resource through each concrete public specification, checks the Erlang shape-one boundary, checks infinite-credit expectations for all three laws, checks Laplace reflection, and exercises decreasing chains at x=0 with arbitrary credits and x=1 with infinite credits. Printed axioms for the three public specifications and both supporting results are exactly `propext`, `Classical.choice`, and `Quot.sound`. No implementation terms were changed. These proofs concern ideal real semantics; Float interpreter rounding is separate.

## Accepted source identities

- `SampLib.Exponential.exponential_distSpec`: `f7c9837b6794ff313afdfc4e967425a94b74f7e1191719014a4b603966b1ba41`.
- `SampLib.Laplace.laplace_distSpec`: `b86d6d8fe853a3eeffd97a6a5f59828e0246146d5fadebac843c7292c9ee5bb1`.
- `SampLib.Erlang.erlang_distSpec`: `208515f4e886a4a5052c294f083562a5ef8143d3ecb39f81e7b92fb2343d8a16`.
- Support `SampLib/Samplers/DecreasingTrial.lean`: `a6f8030faad92ee68747011234287473a2c8f2c945a751b163c02decb19aa60f`.
- Support `SampLib/Distributions/Exponential.lean`: `e5cad1202a7281cc1ea87faec9ddd6381908ff5bc3c906e60c3333739e599cea`.
