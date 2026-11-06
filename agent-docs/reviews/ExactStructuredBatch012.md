# Independent exact sampler review: ExactStructuredBatch012

Reviewer: `/root/review_exact_a`. Accepted core theorem
`SampLib.OptimalTable.optimalDraw_distSpec` (plain `IsDistSpec`), proof file
`SampLib/Samplers/OptimalDraw.lean`, SHA-256
`3b912400a413ea83274ca1d5fc162f1980cf13dc2c07ca6c6c5da248a5f042de`. The new math file
`SampLib/Distributions/OptimalTableLaw.lean` has SHA-256 `d88c3447…9ae8`. Source
`code/Samplers/Weighted/Optimal.lean` hashes to the approved repaired bytes
`a9b71b1c…4571`.

This review replaces my rejection of the narrow `create ws` spec in
[ExactStructuredBatch011](ExactStructuredBatch011.md).

## Domain

Every valid table, as the source tuple `(matrix,(k,(l,rejected)))`:

- Rows are arbitrary naturals `rows : Fin n → ℕ`. The scan reads only the low `k`
  bits, so `weight k l E = decode(2^(k-l), E mod 2^k)`.
- Any `l<k`.
- Any integer rejection label. Scan labels are `0..n-1`, so a label outside that
  range means no rejection.
- `∑ weight = 2^k-2^l`, which is exactly total root mass one.
- Positive accepted mass. This is equivalent to a rejected row mass below one.

The law is `WeightedChoice.law (accepted …)` on row labels, for arbitrary ENNReal
credit. The domain is complete:

- A table whose masses do not sum to one is not a probability matrix.
- If the rejected row has mass one, the draw never terminates.
- `l≥k` breaks the column arithmetic of the source.

## Mathematics

- `tail_zero_eq` drops the bits above `k` (`bit_mod`). It then reuses the
  previously reviewed prefix/block identity.
- `root_mass` turns the numerator sum into the `Σ tail = 1` hypothesis of the
  general `OptimalWalk.twp_walk`.
- `restart_expectation` splits root credit into accepted mass `A` and rejected mass
  `B`, with `A+B=D`. A rejection leaf receives `C+Kε`. The expectation is then
  `C+(BK/D)ε`, so this needs `BK≤D` and `K>1`.

### Retry factor

The prover's objection to my earlier suggestion is correct. With `p=B/D`, a valid
factor needs `1<K≤1/p`. My `K=1/(1-p)=D/A` gives `BK/D=B/A`, which is at most 1
only when `p≤1/2`. That holds for generated tables but not for arbitrary ones.

`K=1+A/D=2-p` is the right choice:

- `p(2-p)≤1` always, since this is `(1-p)^2≥0`. In the proof, `hbudget` shows this
  as `BA/D≤A`.
- `K>1` exactly when `A>0`.
- It stays finite at `B=0`, where `1/p` would be infinite.

The caller exercises `p=2/3`.

## Program proof

- `twp_optimalDraw` performs 17 pure steps on the kernel-checked source view, then
  calls `twp_root`.
- `twp_root` uses `twp_err_pos`, `ErrorCredit.Induction.simple` with the new factor,
  a linear restart capability `R`, and the general `twp_walk`.
- The public theorem is a short wrapper.

The proof is straight-line, has no new warnings, and keeps lines within 100 columns.

## Questions from the lead

**(a) The `twp_root` duplication is acceptable.** About 25 lines repeat the standard
restart idiom from `SampLib/OptimalDraw.lean`. Only the factor and the expectation
lemma differ. Avoiding the repetition would mean deriving the old root from this
one, which would change the frozen closure of Batch011. The repeated part is a
template, not mathematics.

**(b) Keeping `SampLib.Optimal.optimalDraw_distSpec` is acceptable.** It is a
specialization: `create ws` is a valid table whose accepted numerators are `ws`.
The caller checks this on `[1,0,4]`, giving rows `[1,0,5,1]`, `k=3`, `l=1`, label
`3`. The campaign row must name `SampLib.OptimalTable.optimalDraw_distSpec`.

The two names collide across namespaces. When OptimalChoice is next re-receipted,
I recommend renaming the old one or deriving it from the new spec. Until then,
leave it in place.

## Checks

- Build: `lake build SampLib.Samplers.OptimalDraw` passes.
- Caller: [ExactStructuredBatch012Callers.lean](ExactStructuredBatch012Callers.lean)
  compiles. It frames an arbitrary resource on hand-made tables:
  - `[1,2]` with `k=2`, `l=0` and no label.
  - The same rows with label `1`, so `p=2/3`, and infinite credit.
  - A certain all-ones row `[3,0]` with `k=2`, `l=1` and out-of-range label `7`.
  - Rows `[5,10]`, whose high bits are ignored.
- Pure kernel checks:
  - The rejected label gets zero mass.
  - A certain rejected row has zero accepted mass and is excluded.
  - A table with mass below one is excluded.
  - The generated table is an instance of the domain.
- Axioms: the public spec, `twp_root`, `restart_expectation` and the caller use only
  `propext`, `Classical.choice` and `Quot.sound`.
