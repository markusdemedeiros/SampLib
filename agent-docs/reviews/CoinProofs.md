# Independent review: coin sampler proofs

Reviewer: `/root/review_coins`. Scope: five basic combinators, four recursive
factories/counts, and three elementary factories. The existing `RealCoin` and
`VonNeumann` proofs are baselines and are not new sampler counts.

A sampler is accepted only after source/spec review, an independent clean module
build, an axiom audit, and a representative caller or endpoint check. Draft files
and author reports alone do not establish acceptance.

## Review criteria

- The theorem concerns the existing `pl%` term with its ordinary full domain.
- The stated output law is mathematically recognizable and normalized.
- Credits remain arbitrary in `ℝ≥0∞`, including infinity.
- Each callback call uses its distribution specification; concrete fair-coin
  helpers have proved specs rather than permanent assumptions.
- Recursion has an explicit valid total-correctness/amplification argument and
  includes every terminating boundary claimed by the source.
- The program proof is simple symbolic execution under fixed CTE idioms.
- One central expectation lemma displays the mathematical argument. Routine
  normalization facts and representation helpers do not obscure it.
- Scopes, comments, and formatting follow `agent-docs/VerifyingSamplers.md`.
- There are no `sorryAx` or newly introduced axiom dependencies.

## Baseline assessment

`IsDistSpec` is appropriate for Boolean callbacks: its probability-measure
requirement prevents mass-inflation specs, it allows arbitrary continuation
credits, and its typed postcondition retains the returned Boolean. Its `wp` rule
holds the caller's linear continuation resources across the sampled call.
No baseline change is required for this review scope.

## Sampler status

| Sampler | Author | Verdict | Evidence / required work |
| --- | --- | --- | --- |
| `complement` | `prove_coin_combinators` | Accepted | Full `[0,1]`; negation swaps masses; endpoint and resource checks. |
| `coinProduct` | `prove_coin_combinators` | Accepted | Full `[0,1]²`; output bias `pq`; endpoint/infinite-credit/resource checks. |
| `coinDisjunction` | `prove_coin_combinators` | Accepted | Full `[0,1]²`; output bias `1-(1-p)(1-q)`; endpoint/resource checks. |
| `coinMean` | `prove_coin_combinators` | Accepted | Full `[0,1]²`; actual proved integer fair coin; arithmetic-mean and resource checks. |
| `coinConditional` | `prove_coin_combinators` | Accepted | Full `[0,1]³`; output bias `rp+(1-r)q`; selector endpoints/resource checks. |
| `oneDivOnePlus` | `prove_recursive_coins` | Accepted | Full `[0,1]`; amplification2, actual fair primitive, endpoint/infinity/resource checks. |
| `evenParity` | `prove_recursive_coins` | Accepted | Full `0 ≤ p < 1`; valid inequality amplification; `p=0` and resource checks. |
| `bernoulliRace` | `prove_recursive_coins` | Accepted | Full `p+q>0`; zero sides and two unit sides included; ratio-law and resource checks. |
| `geometricFailures` | `prove_recursive_coins` | Accepted | Full `p<1`, including p=0; arbitrary signed offset; canonical geometric law and resource checks. |
| `oneMinusOverOnePlus` | `prove_elementary_factories` | Accepted | Full `[0,1]`; exact extra-credit allocation covers p=1; endpoint/infinity/resource checks. |
| `onePlusHalf` | `prove_elementary_factories` | Accepted | Full `[0,1]`; direct input tail call; endpoint/infinity/resource checks. |
| `complementHalf` | `prove_elementary_factories` | Accepted | Full `[0,1]`; reuses reviewed complement/mixing mathematics; endpoint/infinity/resource checks. |

## Suggestions and resolutions

The initial `EvenParity.bias` proof fed several derived facts into `nlinarith`.
I suggested direct positive-denominator and `div_le_one` bounds. The author
implemented that change before the accepted snapshot. The final construction is
three lines and states the two interval bounds directly.

No unresolved blocking issue remains in the accepted snapshots. In particular,
`CoinMean` calls `FairCoin.fairCoin_distSpec`; it does not retain an unproved
concrete helper assumption. It legitimately specializes the already reviewed
conditional-mixture expectation instead of duplicating scalar algebra.

## Independent validation: first six accepted snapshots

Each source was independently re-elaborated using `lake env lean` on its actual
file, with an empty warning/error log under `/tmp/review-coins/`. The five initial
modules were checked by a single sequential command, and `CoinMean` separately.
The author builds were also inspected, but are not the sole evidence.

`lake env lean /tmp/review-coins/BasicAudit.lean` checks:

- public-spec axiom dependencies for all six samplers;
- product/disjunction biases at both operand boundaries;
- conditional-selector boundaries `r=0` and `r=1`;
- complement boundaries and even-parity's deterministic `p=0` law;
- arithmetic-mean bias as an equality of real probabilities;
- explicit `∞` continuation credits at zero-probability and unit-probability events;
- a caller retaining arbitrary linear `I : IProp GF`, instantiated separately
  with each accepted public spec.

All six public specs depend only on `propext`, `Classical.choice`, and `Quot.sound`.
There are no finite-credit restrictions or uniform-real assumptions. The five
abstract-only samplers are generic over the lawful real model; `CoinMean` adds
only the integer-uniform primitive required by its actual implementation.

### Reviewed file hashes and public specs

The SHA256 hashes below bind these verdicts to the reviewed source. Root must
revalidate a changed file rather than retain an earlier acceptance automatically.

- `SampLib/Samplers/Complement.lean`
  - Spec: `SampLib.Complement.complement_distSpec`
  - SHA256: `14fe9d358c7bfd2c6459bce36346471bda0b4310b22534819d393ad8f77f6ad1`
- `SampLib/Samplers/CoinProduct.lean`
  - Spec: `SampLib.CoinProduct.coinProduct_distSpec`
  - SHA256: `6076fb895ff229084c3bb686c602174b8a0078d55e8a25e05eb23ccf5750148a`
- `SampLib/Samplers/CoinDisjunction.lean`
  - Spec: `SampLib.CoinDisjunction.coinDisjunction_distSpec`
  - SHA256: `4f2c8995ebbaa218444dc8aa0d9874be70ad0c974dd754314622fc01e9ca86cf`
- `SampLib/Samplers/CoinMean.lean`
  - Spec: `SampLib.CoinMean.coinMean_distSpec`
  - SHA256: `b14b21db0060327b79d8faf02fc046f9a75166937fa54692474752cdc317ecd4`
- `SampLib/Samplers/CoinConditional.lean`
  - Spec: `SampLib.CoinConditional.coinConditional_distSpec`
  - SHA256: `8dfb54937be016a4105dc511c47a9dcede2258527b7fba6c166d56477e8b4b8a`
- `SampLib/Samplers/EvenParity.lean`
  - Spec: `SampLib.EvenParity.evenParity_distSpec`
  - SHA256: `bbc8c559e0d1461bdcbbc39bb6a71cbfa9d558379040fcd507959c6d6ac00e90`

## Additional accepted snapshots: elementary and reciprocal factories

`OnePlusHalf` initially re-bound its tail call to the abstract coin, then manually
returned and repacked the result. I suggested applying `hcoin.spec` directly. The
author made this change and independently rebuilt both it and `ComplementHalf`.
The shortened branch now follows the tail-call idiom already used in
`CoinProduct`; the source remained otherwise unchanged.

`OneDivOnePlus` had an overlong coefficient-normalization line. I required the
formatting fix and suggested a `simp only` replacement. The author tested the
latter, found a real coercion/transparency mismatch, and retained the stable
explicit `change`, wrapped below 100 columns. This is resolved: the intended
coefficient equation remains stated and the CTE program proof contains no algebra.

For `OneMinusOverOnePlus`, I checked the auxiliary-credit allocation directly:
input-true exits discard `ε`, while the only retry gets `2ε`. Their combined
expected extra credit is `(p + (1-p))ε = ε`, so both endpoint biases are included
without a singular amplification factor. The target recurrence and program
branches match the existing sampler.

All four final sources were independently re-elaborated with empty warning/error
logs. The expanded `/tmp/review-coins/BasicAudit.lean` compiles warning-free and
adds their target-bias endpoints, zero-mass/infinite-credit checks, separate
arbitrary-resource callers, and public-spec axiom audits. All dependencies remain
`propext`, `Classical.choice`, and `Quot.sound` only.

- `SampLib/Samplers/OnePlusHalf.lean`
  - Spec: `SampLib.OnePlusHalf.onePlusHalf_distSpec`
  - SHA256: `52133949e5c7b46a966d49c245480be5f7e3f0e5634ed08f247e7a970c6e2aee`
- `SampLib/Samplers/ComplementHalf.lean`
  - Spec: `SampLib.ComplementHalf.complementHalf_distSpec`
  - SHA256: `b6a1a75c18fe531594c251396dea9198d7cf93ba0061b147c6815f2fd638fe92`
- `SampLib/Samplers/OneMinusOverOnePlus.lean`
  - Spec: `SampLib.OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec`
  - SHA256: `c4c734b9d4936b16ccc5bb241c59912c61246de0bc1202ecef4dfa785260183b`
- `SampLib/Samplers/OneDivOnePlus.lean`
  - Spec: `SampLib.OneDivOnePlus.oneDivOnePlus_distSpec`
  - SHA256: `b8bda61742103fb88f85e411ef6ae0173e4ad059279c58cd0faa2fff3dea49dd`

## Final two accepted snapshots

`BernoulliRace` matches the actual selector/left/right control flow. Its success
bias is `p/(p+q)` on the full terminating domain `p+q>0`; either individual coin
may have bias zero, and the all-success case `p=q=1` is included. Its factor
`2/(1+retryProbability)` is greater than one on that domain and gives an expected
termination-credit coefficient at most one. No strictly-positive requirement was
silently added to either individual bias.

`GeometricFailures` counts true inputs until the first false, so the canonical
geometric law uses stop probability `1-p`. It covers every `p<1`, including zero,
and returns `offset+n` for an arbitrary integer offset. The mathematical identity
`p(2-p)+(1-p)^2=1` exactly accounts for amplified retry credit and spare stopping
credit. The main proof reverts both offset and continuation credit before the
persistent induction step, then applies the shifted continuation on recursion.
This preserves linear resources correctly.

I also independently re-elaborated `SampLib/Distributions/Geometric.lean`, checked
its sum-of-Dirac recurrence for arbitrary ENNReal credits, and audited its axioms.
It specializes correctly at stop bias one; the caller audit derives the resulting
Dirac law from singleton masses rather than assuming a missing mathlib simp lemma.

Both final sources and this support module re-elaborate without warnings. Their
public-spec/helper axiom audits are standard-only. The final persistent caller
artifact also checks the race's individual-zero and all-success boundaries,
negative geometric offsets, infinite credits on zero-probability count events,
and a separate arbitrary-resource caller for each new spec.

- `SampLib/Samplers/BernoulliRace.lean`
  - Spec: `SampLib.BernoulliRace.bernoulliRace_distSpec`
  - SHA256: `b0efbaf37a5bb2824ff3ea5ee427d0bd3f840a3fb9fbd6dca6f4a5098d21f454`
- `SampLib/Samplers/GeometricFailures.lean`
  - Spec: `SampLib.GeometricFailures.geometricFailures_distSpec`
  - SHA256: `03b527b3700fcb7ab28a4b7ee8434f38098a57e8b3526ff7b59d4024c6dbeedc`

Reviewed support SHA256: `f35eaf7977331250eb2152791b93d048be5f60d05e2c82a584a4d2b781624bd5`.

## Reproducible final evidence

The final caller, boundary, infinity, and axiom checks are persisted in
[CoinCallers.lean](CoinCallers.lean). Re-run them with:

```sh
lake env lean agent-docs/reviews/CoinCallers.lean
```

The artifact instantiates a linear-resource continuation separately for each of
the twelve accepted specs. It also composes the proved integer fair coin as an
actual input to complement, reciprocal extraction, and shifted geometric counting.
It imports the individual reviewed modules, so its evidence does not depend on a
broad project-root import accidentally supplying extra hypotheses.

A final targeted `lake build` of all twelve modules passed without warnings
(`/tmp/review-coins/FinalBuild.log`). Every source was also directly re-elaborated
independently; those logs are under `/tmp/review-coins/` by module basename. The
persistent artifact compiles without warnings and all thirteen printed axiom sets
(the twelve public specs and geometric recurrence helper) are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

[CoinProofs.json](CoinProofs.json) is this reviewer's machine-readable acceptance
receipt. Its source snapshots cover the implementation and full project-local
import closure. Its context pins the toolchain, Lake files, proof policy, and all
clean git dependency HEADs. The final caller checks were replayed against that
context, and snapshots were compared afterward to prevent accepting a concurrent
source refresh. Accepted status was derived from this review, not from the root
campaign manifest.

Caller artifact SHA256: `2a5ad5a541c753b5c85f0f305c3315d41c61fa0243915b595ab5a91ae01ab57a`.
