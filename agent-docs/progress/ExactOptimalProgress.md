# Exact optimal-choice work

> Round-2 working notes, kept as a record and not updated since 2026-11-06. For current
> status see [LAWS.md](../../LAWS.md) and [the deferral list](../ExactCampaignDeferrals.md).

Owner: `weighted` team (round 2), transferred from `prove_constants` and before that
`prove_weighted`. Scope: `Occil.WeightedVariants.optimalDraw` and `optimalChoice`.
Both proofs are complete and await independent review; nothing here is acceptance.

## Source repair

Root applied the independently approved endpoint repair in `Optimal.lean`
(`ExactOptimalSourceRepair001`; archive under `reviews/optimal-certain-repair/`).
Canonical SHA, unchanged by the proofs:
`a9b71b1c8b8bfa72602ac4693c83ff2eb0dccb5a98fab661d37c7c534aa44571`.
Runtime evidence: `OptimalRepairRuntime002` (88 tables, 528 interpreter runs).

## Status

- `optimalChoice`: **accepted** in [ExactStructuredBatch011](../reviews/ExactStructuredBatch011.json)
  (`SampLib.Optimal.optimalChoice_distSpec`, plain, core). Its whole snapshot is frozen,
  including `OptimalDraw`, `OptimalRejection`, `OptimalWalk` and `Samplers/OptimalChoice`.
- `optimalDraw`: the first submission covered only `create ws` tables and was rejected. A
  general spec now awaits review: `SampLib.OptimalTable.optimalDraw_distSpec` in the new module
  `SampLib.Samplers.OptimalDraw`. It is plain `IsDistSpec` and core. The frozen
  `SampLib.Optimal.optimalDraw_distSpec` stays as it is; it is superseded, not the public spec.

## General optimalDraw

Domain: every table `⟨List.ofFn rows, k, l, rejected⟩` with arbitrary natural rows
`rows : Fin n → ℕ` (any size; only the low `k` bits are scanned), `l < k`, and any
integer `rejected`. Validity has two conditions:
- `∑ i, weight k l (rows i) = 2^k - 2^l`, which means the root masses sum to 1;
- `[NeZero (acceptedMass rows k l rejected)]`, which means the rejected row's mass is below 1.

A rejected label outside `[0, n)` means no rejection. The law is `WeightedChoice.law
(accepted rows k l rejected)`, the row numerators with the rejected row set to zero.
Arbitrary ENNReal credit is supported.

Math: `Distributions/OptimalTableLaw` (new). `tail_zero_eq` reads row mass as
`weight/D` via `bit_mod`. `restart_expectation` is the single expectation lemma.
Retry factor `1 + A/D` (A = accepted mass), because `B(1 + A/D) ≤ D` for every rejection
mass `B < D`; the factor `1/(1-p)` would need `p ≤ 1/2`. CTE: `twp_root` copies the frozen
root argument with this factor, then reuses frozen `OptimalWalk.twp_walk`; `twp_optimalDraw`
opens the source.

Checks: `lake build SampLib.Samplers.OptimalDraw` is clean, and `#print axioms` gives
`propext, Classical.choice, Quot.sound`. Caller `reviews/WeightedRound2Callers.lean`
(`tableFramed`) frames an arbitrary resource and covers three hand-built tables:
- k=3, l=1, rows [9,2,3] with label 2 rejected: an unreduced row, rejection mass 1/2;
- rows [1,6] with label 1 rejected: rejection mass 5/6;
- the all-ones row [0,7] with no rejection.

All 44 Batch011 snapshot hashes were rechecked after the work and are unchanged.
