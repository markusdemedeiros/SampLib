# Exact factories batch 031

Reviewer: `/root/review_exact_a`.

The proof verifies the actual reverse-time Bernstein-envelope source. `Program.source_eq` ties the
proof's syntax to `Occil.FactoryExtra.envelopeFactoryDegrees` itself. One owned fresh uniform bag
serves every comparison. Each round runs the steps below.

- It calls the deterministic `next` callback.
- It draws a fresh binomial block through the coin's `IsDistSpec`. Credit transport for this
  block is the expectation lemma `Coefficients.expectation`.
- It reads the new row and computes the exact hypergeometric conditional averages of the previous
  row. These are verified as executed, against the raw signed fractions.
- It rescales the thresholds and makes two owned-uniform comparisons that refine the same dyadic
  posterior.

An unresolved comparison has positive width, so every division that runs after survival has a
nonzero denominator. Termination uses `twp_err_pos` with a finite horizon. The unresolved mass
equals the Bernstein width `upperMean N p - lowerMean N p`, which tends to zero. The limit
identifies the initial cost as `RealCoin.credit target F` for arbitrary ENNReal `F`.

The spec kind is `plain`, which is correct because the bag is private and never returned.

## Domain

An earlier pass of this review rejected a contract that required convergence at every bias. That
contract excluded valid factories on the open unit interval, such as functions discontinuous at
p = 0. The current `Parameters p` requires the lower and upper Bernstein means to converge to a
common `target` only at the input `p`. The rest of the coefficient contract is unchanged:

- degree 0 = 0, and degrees strictly increase;
- the rows are rational and satisfy 0 <= lower <= upper <= 1;
- the initial row is 0/1;
- the rows satisfy reverse-hypergeometric degree-elevation consistency.

The callbacks are deterministic. `bounds` must realize exactly the visited positive rows, with any
raw signed unreduced fractions. `next` maps `degree t` to `degree (t+1)`.

The domain includes input biases 0 and 1 and targets 0 and 1. `envelopeFactory` adds
`degree t = t`, which its `n + 1` callback discharges. I compared the changed files
(`EnvelopeCoefficients`, `EnvelopeHorizon`, `EnvelopePosterior`, `EnvelopeFactory`) against the
previous pass. The only change in meaning is the localization of convergence to `p`. The program
proofs are unchanged.

## Accepted sources

- `Occil.FactoryExtra.envelopeFactoryDegrees`:
  `SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec`, core.
- `Occil.FactoryExtra.envelopeFactory`: `SampLib.EnvelopeFactory.envelopeFactory_distSpec`,
  derived.

Both specs are proved in the same file. Proof SHA256:
`9f2dc08cffc0ae3a0dbd023622a9a4c696b312abba2f4eb27b6894dc05cbaff3`.

## Evidence

- `lake build SampLib.Samplers.EnvelopeFactory` succeeds. No line in the envelope closure exceeds
  100 columns.
- The independent caller is [ExactFactoriesBatch031Callers.lean](ExactFactoriesBatch031Callers.lean).
  It compiles without warnings or errors and covers the following.
  - Both public specs preserve an arbitrary framed Iris resource and arbitrary credits.
  - A `Parameters p` is built from any `Coefficients` together with convergence at `p` alone.
  - Both specs compose with the verified fair coin.
  - At p = 0 with target 0 and at p = 1 with target 1, infinite credit sits on the null outcome
    at zero cost.
  - At p = 0, infinite credit sits on both outcomes.
- The exact-source-head and noncircular-premise audits pass for both specs.
- The two public specs, `twp_envelopeFactoryDegrees`, `Parameters.exists_horizon` and
  `Coefficients.expectation` print only `propext`, `Classical.choice`, `Quot.sound`.
- The receipt binds the full 55-file project-local source closure and the dependency context.
