# Exact entropy recycler proof

## Status (round 2, `prove_series`)

Both samplers are built and await independent review. The implementation is unchanged.

| Sampler | Public spec | spec_kind | Classification |
|---|---|---|---|
| `Occil.Weighted.recycledUniform` | `SampLib.RecycledUniform.recycledUniform_ownedDistSpec` | `owned` | support (`voseDraw` precedent) |
| `Occil.Weighted.recycledSamples` | `SampLib.RecycledSamples.recycledSamples_distSpec` | `plain` | core |

- `recycledUniform`: `P = pool ↦ (0,1)` and `n > 0`, with uniform law on `[0,n)`.
  The pool is reset after every draw. This is the state the source allocates, and
  every draw preserves it. For an arbitrary valid stored pool `(v,w)` with `v < w`,
  the stronger joint theorem `RecycledUniform.twp_recycledUniform` uses the
  normalized kernel `EntropyPool.recycledLaw n v w`. That kernel covers result, new
  rank and new width, accepts arbitrary ENNReal credits, and returns ownership of the
  updated pool. This joint contract has no registered `spec_kind`. It is offered as
  the full-state statement and is not used for the `owned` row.
- `recycledSamples`: every positive bound `n` and nonnegative count. The law is
  `SampleWithReplacement.law (UniformInt.law n) count`, decoded as a list.
  `recycledSamples_zero_distSpec` covers the remaining source-accepted inputs:
  count `0` with any integer bound, which returns `[]`. Negative counts fail.
- Modules: `SampLib/Samplers/RecycledUniform.lean` and
  `SampLib/Samplers/RecycledSamples.lean`. Their closure includes the support listed
  below. Owner callers are in `agent-docs/reviews/SeriesCallers.lean`.
- Round-2 support repairs: `EntropyPoolLoop.twp_loop_horizon` had stale
  pure-step counts around `rand`. It now reads: two pure steps, the bit, then two
  pure steps. `EntropyPoolEntry.twp_recycledUniform_reject` now normalizes the
  residual call with `loop_openRec/closeRec` and drops an unused hypothesis.
- Program proof: `twp_bounded` removes the horizon with `twp_err_pos`,
  `BitRecycler.exists_horizon` and `horizon_lintegral_bound`. Rejection
  continues in the bounded loop. Acceptance uses `twp_recycledUniform_accept`.


Owner: `prove_series`. This covers the original `recycledUniform` and
`recycledSamples` rows. `prove_weighted` handed off both existing EntropyPool
support modules and its accepted-rectangle fixture; those modules are support,
not independently accepted sampler proofs.

## Essential distinction

A fixed known pool `(v,w)` need not produce a uniform next output. Its public
specification must use a normalized joint kernel on `(result,v',w')`, accept
arbitrary ENNReal credits, and return ownership of the updated physical pool.
Do not use a uniform `IsOwnedDistSpec` for arbitrary/existential pool contents.

There is a useful stronger source-specific fact: whenever execution requests a
fresh bit, its current width is below `n`. The doubled width is below `2n`, so
any later acceptance has quotient exactly one and stores `(0,1)`. Consequently,
from the actual newly allocated `(0,1)` state, every complete draw returns the
same state. An owned uniform spec is valid for this precise invariant and composes
with `twp_repeatSample_owned` to prove IID batches.

## Mathematical reduction

Let `q=w/n`, `A=q*n`, `r=w%n`. For valid `v<w` and `n>0`:

- If `v<A`, the joint law is the deterministic outcome `(v%n,v/n,q)`.
- Otherwise, `r>0`, `v-A<r<n`; the future is bounded-width lower bit recycling,
  and every accepting leaf has final pool `(0,1)`.
- When `w<n`, `A=0` and `r=w`, so the same rejection formula applies without
  any real deterministic rejection step.

`Distributions/EntropyPoolAbsorption.lean` constructs the bounded fixed-rank law.
`stopped n T w v F` pays accepted leaves before `T` bits and zero elsewhere.
Its finite output matrix has entries `stopped ... (indicator {j})`.
`mass n w v j` is their increasing supremum. The main facts are:

1. Existing `BitRecycler.credit` equals `stopped` plus the unit-debt tail.
2. For valid bounded states the tail is at most `(n-1)/2^T` and tends to zero.
3. Finite matrix linearity holds for arbitrary ENNReal `F`, including infinity.
4. Summing all eventual output masses is one (finite sums, monotone convergence,
   and accepted-plus-tail conservation).
5. The finite Dirac sum `boundedKernel` is therefore a probability measure under
   explicit validity proofs (`boundedLaw`). Its expected credit plus the tail
   funds each finite source execution.

For the ensemble theorem, pair each rank with its fresh bit. At each finite
horizon, the sum of accepted point masses over all starting `v<w` is independent
of the requested output `j<n`: a full accepted block contains each output once,
while the residual interval has the same inductive property. Taking monotone
limits and using normalization gives

`sum_{v<w} mass(n,w,v,j) = w/n` for `w<n`, `j<n`.

The general joint ensemble splits by `EntropyPool.rectangle` / `split`:

`sum_{v<w} E[F] = sum_{k<q} sum_{j<n} F(j,k,q)
                  + (r/n) * sum_{j<n} F(j,0,1)`.

After division by `w`, output is uniform and independent of a residual-pool law
which is conditionally uniform on its width. Equivalently, that residual law is
`(n/w) * sum_{k<q} delta(k,q) + (r/w) * delta(0,1)`.
The special actual starting width one gives uniform output and reset pool.

## Source proof structure

Use a private exact copy/raw AST of the source's local two-argument loop.
Heap ownership remains the *original stored pair* while local ranks/widths evolve;
the heap is changed only on acceptance. Do not identify the stored heap with each
intermediate local rank.

Prove bounded-width finite-horizon CTE by induction on bit count using the
existing lower `BitRecycler.credit`. Each step:

1. Executes the `width<n` branch and samples the one actual uniform bit.
2. If doubled width stays below `n`, applies the smaller horizon directly.
3. Otherwise, uses quotient-one arithmetic. An accepted rank stores `(0,1)`;
   a rejected rank subtracts `n` and applies the smaller horizon.

The heap precondition may own any old stored value; the loop only preserves it
until the final store. A continuation-shaped deterministic wide-step helper will
keep this program proof straight-line. Existing `EntropyPool.twp_recycledUniform_accept`
is useful for immediate top-level rectangle acceptance.

Remove the horizon with `twp_err_pos`, the exact eventual fixed-state expectation,
and `BitRecycler.exists_horizon`. The public all-state joint contract then follows
by immediate acceptance or a single deterministic rejection into the bounded
loop. Prove source syntax correspondence explicitly; do not insert FDR calls or
replace the implementation.

For `recycledSamples`, allocate the actual initial pool and instantiate the
precise reset-state `IsOwnedDistSpec`. Reuse `twp_repeatSample_owned`, covering
count zero and bound one. All source code remains unchanged; no FFI primitives.

## Current files and ownership

- `Distributions/EntropyPool.lean`: existing clean rectangle/split/joint-credit math.
- `SampLib/EntropyPool.lean`: existing clean accepted-rectangle source/store rule.
- `Distributions/BitRecycler.lean`: frozen existing finite-horizon lower/upper model;
  consume without editing.
- `Distributions/EntropyPoolAbsorption.lean`: new bounded-law, finite-matrix,
  normalization, tail, and uniform-ensemble development in progress.
- `Distributions/EntropyPoolKernel.lean`: full joint fixed-pool kernel, deterministic
  residual-state function, arbitrary-credit horizon bound, and uniform-ensemble
  product law.
- `EntropyPoolLoop.lean`: root owns the exact local loop, its pure opening gateway,
  quotient-one wide step, and bounded-width source horizon rule. Do not edit it
  from this lane.
- The full top-level source wrapper, general wide rejection transport, and batch
  integration remain with `prove_series`.

All Lean checks use `python3 agent-scripts/lean_gate.py -- ...`, one target.
