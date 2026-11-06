# Exact discrete samplers: progress

> Round-2 working notes, kept as a record and not updated since 2026-11-06. For current
> status see [LAWS.md](../../LAWS.md) and [the deferral list](../ExactCampaignDeferrals.md).

Owner: `prove_series` (round 2). Both rows below are ready for independent review.
Neither changes its implementation in `code/`.

| Sampler | Status | Public spec | spec_kind | Classification |
|---|---|---|---|---|
| `Occil.DiscreteExtra.zeta` | built, awaiting review | `SampLib.Zeta.zeta_distSpec` | `plain` | core |
| `Occil.DiscreteExtra.polyaRational` | built, awaiting review | `SampLib.PolyaRational.polyaRational_distSpec` | `plain` | core |

Owner caller evidence: [SeriesCallers.lean](../reviews/SeriesCallers.lean). It frames an
arbitrary Iris resource, exercises boundaries, and prints axioms. Every public spec
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Zeta

- Proof module: [Samplers/Zeta.lean](../../SampLib/Discrete/Zeta.lean). Support:
  `Distributions/{Zeta,ZetaWeights,DyadicBlocks,DyadicPower,DyadicProposal}.lean` and
  `ZetaSyntax.lean`.
- Domain: integers `a,b` with `0 < b < a`; the source fails otherwise. Hence the
  spec takes naturals `a b` with `0 < b` and `b < a` (exponent `a/b > 1`).
- Output: `Val.int n`, `n ≥ 1`. `Zeta.law_singleton` gives
  `law {n+1} = (n+1)^(-a/b) / ∑' m, (m+1)^(-a/b)`.
- Mathematics: a geometric level with success `1 - 2^(1-a/b)`, a uniform rank in the
  dyadic block, and acceptance `(2^l/value)^(a/b)`. The accepted-proposal identity
  (`Zeta.expectation`) conserves arbitrary ENNReal credit and pays retry slack.
- Round-2 repairs: the complement moment is now stated at the actual
  `rationalPowerCoin` bias. The proposal callback is normalized as a `ClosedExp`, so
  the loop no longer needs a raised heartbeat limit. The returned block value
  closes by `rfl`.

## polyaRational

- Proof module: [Samplers/PolyaRational.lean](../../SampLib/Discrete/PolyaRational.lean).
  Mathematics: `Distributions/NegativeBinomialShape{,Base,Proposal,Rising}.lean`, which
  are consumed unchanged.
- Domain: integers `A,B,s,t` with `A > 0`, `B > 0`, `s > 0`, `s ≤ t`; the source
  fails otherwise. The spec takes naturals with those hypotheses. Shape `A/B` is
  any positive rational. Success `s/t ∈ (0,1]` includes `p = 1`.
- Output: `Val.int n` with law `NegativeBinomialShape.law (A/B) (s/t)`, i.e. mass
  `multichoose (A/B) n · p^(A/B) · (1-p)^n`.
- Mathematics: the proposal is the existing integer negative binomial with shape
  `M = ⌈A/B⌉ = (A+B-1)/B`. The source's integer products are
  `rising A B k / rising (M·B) B k`, which equals `multichoose(A/B,k)/multichoose(M,k)`
  (`ratio_bias`). Accepted mass is `p^(M-A/B) > 0`. `expectation_preservation` is
  the single accepted-proposal identity.
- Program: `twp_products` executes the deterministic product recursion by induction
  on the remaining count. `twp_loop` is the usual `twp_err_pos` plus
  `ErrorCredit.Induction.simple` retry proof. The top-level theorem needs
  `maxHeartbeats 1000000` for its first beta step, which opens the large source body.
