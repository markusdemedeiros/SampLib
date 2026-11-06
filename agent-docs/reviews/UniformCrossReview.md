# Independent cross-review: integer primitives and ranges

Reviewer: `prove_finite_trials`. Authors: `prove_uniform` and `prove_ranges`.
This is an additional review independent of `review_discrete`.

## Verdict

All six samplers below are accepted at the recorded source hashes. Their actual
ProbLang terms, full ordinary input domains, target measures, and core proof
steps were inspected. No sampler implementation was changed for this review.

| Sampler | Reviewed domain and mathematical law |
| --- | --- |
| `uniformInt` | Every positive natural bound `n`, representing every positive integer input; normalized finite-uniform law on `0,…,n-1`. |
| `fairCoin` | Uniform integer bit followed by equality with one; exact normalized Bernoulli(1/2) law. |
| `rndInt` | Every nonnegative upper bound, including zero; uniform law on `0,…,hi`. |
| `rndIntRange` | Arbitrary signed integer bounds `lo ≤ hi`, including negative singleton intervals; translated inclusive offset law. |
| `rndIntExcRange` | Arbitrary signed integer bounds `lo < hi`; translated uniform law on `[lo,hi)`. |
| `rationalCoin` | Integer inputs `0 ≤ a ≤ b`, `b > 0`, including `a=0` and `a=b`; exact Bernoulli(`a/b`) law. |

The natural bounds in the first and third specs do not restrict valid object-language
integer inputs: positive and nonnegative integers have exactly those natural
representatives. Invalid bounds are correctly excluded by preconditions.

## Mathematical and logical checks

- Finite-uniform normalization uses the installed normalization theorem for a
  nonempty finite set. Exclusive widths are positive; inclusive widths add one.
- Signed range proofs convert only the nonnegative width to a natural. They do
  not assume nonnegative endpoints. `Int.toNat_of_nonneg` is justified by the
  ordering hypothesis before applying the offset sampler.
- Rational rank counting partitions `b` ranks into `a` successes and `b-a`
  failures. Only the finite probability coefficients are converted between
  integers, reals, and ENNReal. No continuation credit is assumed finite.
- The program proofs follow actual guards and callback structure. Rational
  numerator endpoints have their own deterministic branches. Arithmetic guard,
  cast, and rank-normalization facts are hoisted into helpers.
- All specs retain arbitrary ENNReal continuation credits and use only the needed
  uniform-integer primitive assumption, with generic lawful `rT`.
- Each public spec was exercised through `IsDistSpec.wp` in a caller that retains
  an arbitrary Iris resource `I`. These callers use the public interface, not
  implementation unfolding.

## Independent validation

All commands below passed without warnings:

```sh
lake build SampLib.Samplers.UniformInt SampLib.Samplers.FairCoin SampLib.Samplers.RndInt
lake build SampLib.Samplers.RndIntRange SampLib.Samplers.RndIntExcRange
lake build SampLib.Samplers.RationalCoin
lake env lean /tmp/samplib-uniform-cross/PrimitiveClients.lean
lake env lean /tmp/samplib-uniform-cross/RangeClients.lean
lake env lean /tmp/samplib-uniform-cross/RationalClients.lean
```

The client checks establish:

- The uniform singleton formula for arbitrary `n` and `k`, including off-support
  mass zero; the valid singleton primitive call `uniformInt 1`.
- The inclusive upper-bound-zero law and typed `rndInt 0` call.
- Inclusive interval `[-7,-7]` is a point mass at `-7`.
- Inclusive `[-1,0]` and exclusive `[-1,1)` both have expectation
  `(F (-1) + F 0) / 2`, exposing any endpoint or width error.
- Exclusive `[-5,-4)` is a point mass at `-5`.
- Rational numerator zero and numerator equal to denominator give false and true
  respectively, for arbitrary positive denominator; the `1/3` success expectation
  is also checked.

The expectation, core theorem, and public spec for all six samplers were audited
with `#print axioms`. All eighteen declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a new axiom.
Logs are in `/tmp/samplib-uniform-cross/`.

## Suggestions and resolution

The initial exclusive-range public theorem exposed a `letI : NeZero width` in
its result. I suggested indexing the target law by the existing `lo < hi` proof.
The author adopted that change: `law lo hi h` now has its normalized instance,
and `rndIntExcRange_distSpec` returns a direct `IsDistSpec`. This improves caller
readability without restricting the domain or altering the sampler.

RationalCoin's repeated ENNReal qualifiers were shortened with selective namespace
openings at the primary reviewer's request. The final source was rebuilt and its
independent clients and axiom checks rerun. No remaining changes are requested.

## Reviewed source hashes

| File | SHA256 |
| --- | --- |
| `UniformInt.lean` | `a54369681f648188ac924ba76c6bfc84a7458dedb66328d431b307f77f4a978c` |
| `FairCoin.lean` | `24698d03ab4359a0afc0d974d2d1b6a332dea02a71f8e947ef36c9f9e3436f80` |
| `RndInt.lean` | `c109e78be39b055f9e2af6082253a79d32d9d63c3f06be59615f776b8fee0178` |
| `RndIntRange.lean` | `ed36a99e9849300bee6a3fa35d10270ea6fe68f6d25fe1dc457465a24fa05c39` |
| `RndIntExcRange.lean` | `3307969caa795835b6ccc1c68db37333a6902b52859104bf27871ac96c234e51` |
| `RationalCoin.lean` | `d6ab18675de6d3f1fcd7cbd0036bfa174b0032f9d251c6ea4bfe780b02722eed` |
