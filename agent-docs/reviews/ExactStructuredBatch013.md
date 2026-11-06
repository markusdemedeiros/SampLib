# Independent exact sampler review: ExactStructuredBatch013

Reviewer: `/root/review_exact_b`. Both entries are accepted.

## `Occil.Weighted.recycledUniform` (owned, support)

Public spec `SampLib.RecycledUniform.recycledUniform_ownedDistSpec` in
`SampLib.Samplers.RecycledUniform`, SHA-256
`a3671c1466ff46bcfa1dbb895812c5276da79f637cb1ae5f88e5b1161a309f2f`.

Domain: `NeZero n`, with ownership of `pool ↦ (0,1)`. The output is uniform on `[0,n)`, and
the pool returns as `(0,1)`. If `n <= 0`, the source fails.

Honesty of the reset-state domain. In `code/`, the only caller is `recycledSamples`, which
allocates the pool with `newRecycler` as `(0,1)`. From `(0,1)`, the width doubles to a value in
`[n, 2n)`, and every high-tail residual is below `n`. Each acceptance therefore has quotient
1 and stores `(value / n, 1) = (0,1)`. `loopPost` in `EntropyPoolLoop` proves this. So `(0,1)`
is the only reachable pool state, and the owned spec covers every source use. The stronger
`twp_recycledUniform` gives the exact joint law of the remainder and the new pool for every
valid stored rank `value < width`. As with `voseDraw`, this is a stateful helper used by the
user-facing sampler, so the classification is support.

Proof. Termination for the bounded-width phase uses `twp_err_pos` with a finite bit horizon
whose tail is at most `ε` (`BitRecycler.exists_horizon`). `twp_loop_horizon` follows the actual
fresh bits by induction on the horizon. Entry, rejection and acceptance are separate,
straight-line lemmas, and the heap value stays owned until the single store.

Observation, not a defect: from the reset state, no entropy carries across calls, since the
quotient is always 1. Recycling happens only within a call, on rejected high tails.

## `Occil.Weighted.recycledSamples` (plain, core)

Public spec `SampLib.RecycledSamples.recycledSamples_distSpec` in
`SampLib.Samplers.RecycledSamples`, SHA-256
`8e72a83c2d97e4c9ec13e3b3fafc6c750c75aa089ef0ffc08218080c7fea7df1`.

Domain: `NeZero n` and count `>= 0`. The law is the list of `count` IID uniform draws on
`[0,n)`, in sampling order. `recycledSamples_zero_distSpec` also covers count 0 for every
integer bound, which matches the source: `repeatSample` never calls the sampler at count 0.
A negative count fails the source guard, and a positive count with `n <= 0` fails inside
`recycledUniform`. The domain is therefore complete. The proof allocates the pool with
`twp_alloc` and applies `repeatSample_ownedDistSpec` to the owned per-draw spec. That gives
independence from the shared state, not from a scalar marginal.

## Checks

The caller frames an arbitrary Iris resource. It covers the owned spec at `n = 1, 8, 7`,
owned repetition on one reset pool, and the joint theorem on the non-reset pool `(5,6)`. It
also covers `recycledSamples` at counts 0, 1 and 4, and the zero-count spec at bounds `-3`
and `0`. A targeted build and the caller compile without warnings. The printed axioms are
only `propext`, `Classical.choice` and `Quot.sound`. The support files edited this round,
`EntropyPoolLoop` and `EntropyPoolEntry`, are in the bound source closure.
