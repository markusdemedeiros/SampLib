# Exact PSRN vector rejection progress

> These notes record round 2 and stopped changing on 6 November 2026. For the current
> status, see [LAWS.md](../../LAWS.md) and the [deferred samplers](../ExactCampaignDeferrals.md).

Samplers: `newFGMCopula` and `newRectellipse` in
[Distributions.lean](../../code/Samplers/PSRN/Distributions.lean). Both are deferred. No
proof modules exist; no source defect was found.

| Sampler | Status | Intended spec | Domain (actual source guard) | Class |
| --- | --- | --- | --- | --- |
| `newFGMCopula` | deferred | pair-valued latent vector | `d>0`, `-d≤n≤d` (`θ=n/d∈[-1,1]`) | core |
| `newRectellipse` | deferred | pair-valued latent vector | `rx,ry>0`, `sd>0`, `0≤sn≤sd`, `full : Bool` | core |

## Blocker 1: the return value is a pair, not a list

Both sources return `(x, y)`, which elaborates to `Exp.pair`. `IsLatentVectorSpec`
requires `VectorOwns`, i.e. `v = vectorVal handles = listVal id (List.ofFn handles)`.
No list encoding equals `Val.pair a b` (checked in Lean for every `n`), so no
`IsLatentVectorSpec` for these programs is provable. The frozen
`LatentVectorSpec`/`LatentVectorRejection` cannot change, and the auditor checks the exact
`IsLatentVectorSpec` head.

The lead must choose one option. Either option adds a new spec kind and needs an auditor
extension:

- a pair variant: `IsLatentPayloadSpec e world initial (PairOwns P)` plus two coordinate
  `IsViewSpec`s, where `PairOwns P v s := ∃ l r, ⌜v = Val.pair l r⌝ ∗ P l r s`.
  `LatentProduct.pairOwns` already uses this shape for independent pairs.
- a vector spec generalized over the output encoding.

## Blocker 2: missing inline-loop infrastructure

These pieces are needed regardless of the interface. None exists yet.

1. **Three-uniform world inside the loop.** Each round draws `x`, `y` and a threshold
   uniform `u` with interleaved pure closure constructions. Acceptance tests `u`, so the
   accepted world is the 3-uniform product conditioned on the event, and only the `x`, `y`
   views are returned. `LatentProduct.payloadSpec` covers `code left right` (two
   constructors returned as a pair). It does not cover this `let` chain.
2. **Composite comparison views.** FGM compares `2u` with
   `1 + (n/d)·(1-2x)(1-2y)`. Rectellipse compares `x²+y²` with `1 + (sn²/sd²)x²y²`.
   Represented pieces exist: complement `rational − view`, `add`, `multiply` and
   `scaleRational`. They still have to be chained with `MeasurableError` over the
   shared product world.
3. **Termination domain for `less`.** A.s. distinctness on the 3-D (resp. 2-D) product.
   FGM: `u` is independent of `(x,y)` and atomless. Rectellipse: the curve
   `x²+y² = 1+s²x²y²` is Lebesgue-null, including `s=1`, where it is `{x=1}∪{y=1}`.
4. **Inline `rec retry` amplification.** This is `LatentRejectionKernel.twp_newRejection`
   rewritten for an inline body: same credit split and `ErrorCredit.Induction.simple`.
   Team `inline_reject` is building a scalar version. A vector version would condition
   the whole product world through `Conditioning.model`, as `VectorRejection` does.
5. **Laws.** FGM: the acceptance probability given `(x,y)` is `(1+θ(1-2x)(1-2y))/2`, and
   the total mass is `1/2`. The conditional `(x,y)` law is then `PSRNFGM.law θ`, the
   canonical density `1+θ(1-2u)(1-2v)` on `[0,1]²`; that module already proves
   normalization. Rectellipse: uniform on Occil's region
   `{(x/rx)²+(y/ry)² < 1+(sn/sd)²(x/rx)²(y/ry)²}`, in the quarter `[0,rx]×[0,ry]`.
   The `full` case is symmetrized in each sign. The acceptance mass is the region's area,
   `≥ π/4 > 0`.
6. **Rectellipse post-processing.** It needs `scaleRational` on conditioned views, then
   two `fairCoin` branches choosing `x` or `negate x`. This is a sign mixture over a
   pair. `LatentSign` handles only the scalar case.

## Files

- New: this document only. A scratch Lean check
  (`/tmp/claude-1000/-home-agent-occlib/3ec7ac18-99ee-4050-96f5-1834a07b7456/scratchpad/vector_reject/PairNotVector.lean`)
  proves `Val.pair a b ≠ vectorVal handles`.
- `SampLib/Distributions/PSRNFGM.lean` (pre-existing, unchanged) holds the FGM
  density, normalization and expectation identity for step 5.
