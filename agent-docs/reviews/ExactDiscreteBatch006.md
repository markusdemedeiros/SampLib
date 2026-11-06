# Independent exact sampler review: ExactDiscreteBatch006

Reviewer: `/root/review_exact_b`. Both accepted as plain `IsDistSpec`, classification core.

## `Occil.DiscreteExtra.zeta`

Public spec `SampLib.Zeta.zeta_distSpec` in `SampLib.Samplers.Zeta`, SHA-256
`8184966ff8b6bd4da4db2f4c8e12bb23b08705d116000602fc5c79d9f4f40a0f`.

Domain: naturals `0 < b < a`, so the exponent `a/b > 1`. The source fails on `b <= 0` or
`a <= b`, so the domain is complete. The law lives on the naturals, with no mass at 0
(`law_zero`) and mass `(n+1)^(-a/b) / Σ_m (m+1)^(-a/b)` at `n+1` (`law_singleton`). This is
the canonical zeta law, not a restatement of the algorithm. The dyadic proposal also proves
that the series converges (`normalizer_ne_top`).

Proof. The complemented rational-power coin has bias `1 - 2^(1-a/b)` and drives the actual
`Occil.geometric` level. `integerPower`, the uniform rank and the rational-power acceptance
coin `(2^l / value)^(a/b)` are composed from existing specs, not assumed. The single
expectation lemma `Zeta.expectation` reduces to the shared accepted-proposal identity
through the dyadic-block equivalence. `twp_loop` performs straight-line symbolic execution
under `ErrorCredit.Induction.simple`, with the same alignment pattern as accepted Zipf.

## `Occil.DiscreteExtra.polyaRational`

Public spec `SampLib.PolyaRational.polyaRational_distSpec` in
`SampLib.Samplers.PolyaRational`, SHA-256
`5dcf44f6432a5671829cb62b154b4925f582feaf29d5f598890ee78dc6d79423`.

Domain: naturals `A, B, s > 0` and `s <= t`. Every other integer input fails the source
guard. The law is `NegativeBinomialShape.law (A/B) (s/t)` with density
`multichoose(A/B, n) p^(A/B) (1-p)^n` against counting measure. This is the canonical
real-shape negative binomial (Pólya) on failure counts, normalized by the generalized
binomial series. `s = t` gives the point mass at 0.

Proof. The actual integer negative-binomial proposal at shape `⌈A/B⌉` uses its existing spec.
`twp_products` evaluates the source's deterministic product recursion by induction to the two
rising products. `ratio_bias` identifies their quotient with the multichoose ratio. A single
`expectation_preservation` instance of the accepted-proposal identity follows, and the retry
loop is straight-line. `set_option maxHeartbeats 1000000` sits only on the 10-line top-level
wrapper. It covers `twp_pures` over the four-argument source guard, not a poorly structured
proof.

## Checks

The caller frames an arbitrary Iris resource and arbitrary or infinite `F`. It covers zeta at
`2/1`, `3/2` and `101/100`, and Pólya at `s = t`, shape `1/3 < 1`, and shape `7/2`. Independent
law checks cover zeta's zero mass and closed-form singleton, Pólya's closed-form mass, and
`s = t ⇒ dirac 0`. A targeted build and the caller compile without warnings. The printed axioms
are only `propext`, `Classical.choice` and `Quot.sound`. Both source domains match the integer
guards.
