# Finite-trial sampler cross-review

Reviewer: `/root/prove_recursive_coins`, independently of `prove_finite_trials`
and the first reviewer `review_discrete`. No sampler or proof source was edited.

## Verdict

**Accepted:** Binomial, BoundedGeometric, IterateCoin, RandomWalk.
No semantic, trust, endpoint, or proof-protocol blocker was found.

The mathematical measures are normalized independent-trial constructions. They
are not definitions of operational execution distributions. Each file presents a
single successor expectation identity and a finite-induction CTE proof. The
small zero-case simplifications support symbolic execution rather than creating
an unnecessary second mathematical development.

## Mathematical and specification assessment

| Sampler | Target and domain | Assessment |
| --- | --- | --- |
| Binomial | Bernoulli indicator sum, every `n : ℕ` and `p ∈ [0,1]` | The recurrence is the familiar `p`-weighted successor pushforward plus `(1-p)` times the previous sum law. The callback precedes the recursive sum in both code and proof. |
| BoundedGeometric | Failure count capped at `n`, every `n : ℕ` and `p ∈ [0,1]` | Immediate success contributes a mass at zero; failure shifts the previous capped law. The cap atom remains present, including all mass at the cap when `p=0`. |
| IterateCoin | Bernoulli(`p^n`), every `n : ℕ` and `p ∈ [0,1]` | The target interval bounds follow from `0 ≤ p ≤ 1`. The expectation proof isolates multiplication of success probabilities and the corresponding failure coefficient. `n=0` returns true, including `p=0`. |
| RandomWalk | Sum of `n` independent symmetric ±1 steps, every `n : ℕ` | The law is the normalized two-shift convolution. The proof computes the recursive walk before taking its final fair step, matching the implementation's evaluation order. |

The explicit recursive convolution laws are mathematically recognizable targets
on their own. A closed-form binomial coefficient PMF is not required to understand
or use these specifications. This review does not claim that a separate equality
to a particular mathlib distribution constant has been proved.

All public specifications use `IsDistSpec`. The three callback-based samplers
assume a typed Bernoulli input-coin spec, rather than its implementation or only an
unconditional marginal. RandomWalk uses the actual verified `fairCoin` spec and
requires the integer-uniform primitive, with no uniform-real assumption.

All continuation functions range over ENNReal without a boundedness or finiteness
premise. Their domains are countable, so the required measurability is automatic.
The mathematical proofs use nonnegative integration, map identities, and
semiring algebra. Only finite probability coefficients are handled as real
numbers; arbitrary continuation credits are never passed through `toReal`.

## Program-logic assessment

The main proofs are fixed symbolic execution with natural-number induction,
explicit binds, callback-spec applications, and Boolean branches. Mathematical
identities are named before they are used; no distributional search or polynomial
automation appears in the CTE proof bodies.

RandomWalk's seven explicit pure steps intentionally stop at the recursive call.
Replacing them with `twp_pures` or a repeat tactic would risk entering that call
and would make the stopping point less explicit. They should remain fixed steps.

The integer casts match the returned representations. In particular, failure
counts are natural outputs encoded as integers, and RandomWalk's output is an
integer. Guarded negative trial counts are outside the mathematical trial-count
domain; no valid nonnegative count or terminating coin endpoint is omitted.

## Independent checks

All of these commands completed with exit code zero and no warnings:

```sh
lake env lean SampLib/Samplers/Binomial.lean
lake env lean SampLib/Samplers/BoundedGeometric.lean
lake env lean SampLib/Samplers/IterateCoin.lean
lake env lean SampLib/Samplers/RandomWalk.lean
lake env lean /tmp/recursive-coins/FiniteCrossAudit.lean
```

The separate audit checks:

- The core theorem, public spec, and expectation lemma for each sampler: all twelve
  transitive axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- IterateCoin's zero-trial target, including the `0^0` convention.
- Infinite true-outcome credit at `p=0` for positive iteration counts and infinite
  false-outcome credit at `p=1`; both absent outcomes contribute zero credit.
- Infinite credit at the absent count one under `Binomial.law 0 2` and
  `BoundedGeometric.law 0 2`; both integrals are zero.
- The zero-step walk with infinite credit away from its sole output zero.
- The one-trial binomial expectation equals the Bernoulli indicator expectation.
- A caller instantiating Binomial with the actual `FairCoin.fairCoin_distSpec`,
  retaining an arbitrary Iris resource through `IsDistSpec.wp`.

Re-elaboration logs are `/tmp/recursive-coins/cross-*.log`; the audit log is
`/tmp/recursive-coins/finite-cross-audit.log`. These are transient validation
artifacts; the reviewed source and theorem statements are the lasting evidence.

## Nonblocking suggestion

In the three recursively normalized laws, spelling the induction hypothesis
instance as `letI := IH` would explain its purpose more directly than `let := IH`.
This is a small presentation preference, not a correctness issue; no source
change is required for acceptance. No additional closed-form laws, helper lemmas,
or program-logic golf are recommended for this campaign.

## Reviewed SHA256 snapshots

- Binomial:
  `76e53294152ed9586f37315a5f27e7257faca3e9bec707ff404c6653d6a9e996`
- BoundedGeometric:
  `9d38721aa9012b9cd8b33d661ad269d27f3db932df02c266d7cffbced5496ab8`
- IterateCoin:
  `f14b4ee475b3ea318aef1a1c2705d6a687818886abb00b533690629d3478bbfe`
- RandomWalk:
  `b05909d65e4d4416a02ce57de895cd34742fd161b9c89671efd8dcf32f33d2a1`
