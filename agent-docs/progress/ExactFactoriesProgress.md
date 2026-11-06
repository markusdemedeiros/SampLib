# Exact factories progress (polynomials and envelopes)

> Round-2 working notes, kept as a record and not updated since 2026-11-06. For current
> status see [LAWS.md](../../LAWS.md) and [the deferral list](../ExactCampaignDeferrals.md).

Team `factories`, round 2. Scope: the two polynomial factories in
[Polynomials.lean](../../code/Samplers/Bernoulli/Polynomials.lean) and the two envelope
factories in [Series.lean](../../code/Samplers/Bernoulli/Series.lean).
All public specs below print only `propext`, `Classical.choice`, `Quot.sound`.

## Polynomials: reviewed, awaiting ledger integration

`Occil.FactoryExtra.polynomial` and `Occil.FactoryExtra.rationalFunction` already carry an
independent receipt, [ExactFactoriesBatch030.json](../reviews/ExactFactoriesBatch030.json).
Its proof hashes, caller hash and full 50-file source snapshot still match the worktree.
The ledger still lists them `in_progress` only because the receipt has not been integrated.
This round left the proofs and their import closure untouched.

| Sampler | Public spec | Kind | Class |
| --- | --- | --- | --- |
| `polynomial` | `SampLib.PolynomialFactory.polynomial_distSpec` | `plain` | core |
| `rationalFunction` | `SampLib.PolynomialFactory.rationalFunction_distSpec` | `plain` | derived |

Domains are as recorded in the receipt: any `p : unitInterval` and coin callback; a
nonempty signed rational power-basis list with some admissible elevated degree
(strict range in `(0,1)` is a proved sufficient corollary). The rational factory needs
two such lists and `A(p) + B(p) > 0`.

## Envelopes: ready for review

Proof module: [EnvelopeFactory.lean](../../SampLib/Bernoulli/EnvelopeFactory.lean).

| Sampler | Public spec | Kind | Class |
| --- | --- | --- | --- |
| `envelopeFactoryDegrees` | `SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec` | `plain` | core |
| `envelopeFactory` | `SampLib.EnvelopeFactory.envelopeFactory_distSpec` | `plain` | derived |

Domain of `envelopeFactoryDegrees`: every `p : unitInterval` and coin callback with
`RealCoin.law p`; a `Parameters p` contract, that is degrees with `degree 0 = 0` and strictly
increasing, rational rows with `0 ≤ lower ≤ upper ≤ 1`, initial row `0`/`1`,
reverse-hypergeometric degree-elevation consistency, and lower/upper Bernstein means that
both converge at the input bias `p` to `target : unitInterval`. Callbacks: `next` returns
`degree (t+1)` on `degree t` (`NextSpec`); `bounds` returns, at every positive visited degree
and valid head count, any raw signed fraction pair whose values are that row's coefficients
(`Realization`, `BoundsSpec`). Output law `RealCoin.law target`. Bias endpoints and
targets `0`/`1` are included.

`envelopeFactory` has the same domain plus `degree t = t`.

The program uses its own fresh uniform bag, which is never returned, so `plain` is the
right interface. Termination uses `twp_err_pos` with a finite shadow horizon: the unresolved
mass equals the Bernstein width `upperMean N p - lowerMean N p`, which tends to zero.

Review history:

- The first review rejected an every-bias convergence requirement as an unjustified domain
  restriction. `Parameters` now takes the input bias `p` and asks for convergence only
  there, the only place the proof uses it (`Parameters.exists_horizon`). This changed
  [EnvelopeCoefficients.lean](../../SampLib/Bernoulli/Laws/EnvelopeCoefficients.lean),
  [EnvelopeHorizon.lean](../../SampLib/Bernoulli/Laws/EnvelopeHorizon.lean),
  [EnvelopePosterior.lean](../../SampLib/Bernoulli/Support/EnvelopePosterior.lean) and the two public specs;
  the program proof is unchanged.
- One 104-column line in [EnvelopeFuture.lean](../../SampLib/Bernoulli/Laws/EnvelopeFuture.lean)
  is wrapped.
- Team caller: [FactoriesCallers.lean](../reviews/FactoriesCallers.lean) (framed resource,
  composition with the verified fair coin for both specs, a spec built from raw
  `Coefficients` plus convergence at `p` only, and `p = 0`/`p = 1` with infinite credit on
  null events). It compiles without warnings. The older
  `ExactFactoriesBatch031Callers.lean` targets the previous API and is stale.
