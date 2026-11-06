# Proposed optimal-matrix endpoint repair

Canonical source has not been changed. Root owns applying an independently approved patch.

Original: `code/Samplers/Weighted/Optimal.lean`
SHA-256: `cc627b9b7e17370238377d0e2d9f0455ab3c465dc20d0b12b67d8e5e63f16d01`.
The byte-for-byte archive is `Optimal.lean.original`; the exact proposed change is
`proposed.patch` in this directory.

Replace:

```lean
let encoded := (if l = k then m else if l = #0 then m else
  (m / (period - #1)) * period + m % (period - #1));
```

with:

```lean
let encoded := (if m = denominator then ceiling - #1 else
  if l = k then m else if l = #0 then m else
  (m / (period - #1)) * period + m % (period - #1));
```

The full requested domain remains every finite list of nonnegative integer weights with
positive sum, including zeros and certain vectors of arbitrary length. No singleton or
positive-weight-only restriction substitutes for the repair. `optimalDraw` must also work
on the matrix produced for every such list; a wrapper shortcut alone would leave it broken.

## Defect and fixture

The existing fixture `../OptimalCertainRuntime.lean` uses the upstream `bigStepF`/`Comp`
interpreter. Its log shows `optimalMatrix [2,0] = ([4,0],(2,(1,-1)))`. The traversal scans
positions 1 and 0, so both rows have zero bits forever and no outcome can be selected.
The bounded runs exhaust 10000 transitions at seeds 0, 1, and 99; `[1,1]` returns normally.
The same defect occurs with `[0,2]` and general certain vectors.

## Matrix invariant

For generated parameters, `0 ≤ l < k`, put `A = 2^l`, `P = 2^(k-l)`, and
`D = 2^k - 2^l = A(P-1)`. Every row numerator satisfies `0 ≤ m ≤ D`; the row
numerators, including the optional rejection row, sum to `D`.

For a `k`-bit row integer `E < 2^k`, the first `l` bits form a prefix and the final
`k-l` bits repeat. Its exact mass is

`((E / P)*(P-1) + E % P) / D`.

For `m < D`, the unchanged quotient/remainder encoding is
`E = (m/(P-1))*P + m%(P-1)`. Its quotient is below `A`, its remainder is below
`P-1`, and therefore `E < AP`; decoding gives `m` exactly.

For `m = D`, the original formula instead produces `E = AP = 2^k`, outside the
scanned bits. The proposed endpoint is `E = AP-1`, all `k` bits equal to one.
Its prefix is `A-1`, its repeated block is `P-1`, and decoding gives
`(A-1)(P-1)+(P-1)=D`. Equivalently, the infinite bit string is `0.111... = 1`.
Thus the correction preserves row mass and the probability-matrix width invariant.
At each depth the certain row contributes one leaf, leaving one live rank; its unresolved
probability is `2^-depth`, tending to zero.

The `l=0` endpoint was already all ones; the new branch returns the same value there.
Zero rows remain zero. The source's `l=k` fallback is unreachable for generated valid
inputs: `k=bitLength(total)>0`, `total<2^k`, so the first candidate `2^k-1` is at least
the total and establishes a selected index below `k`. The patch does not create a new
claim for arbitrary malformed tables outside the generated-matrix domain.

Formal cyclic encoding and source CTE proofs are being developed in new modules;
independent source repair review precedes any canonical edit.
