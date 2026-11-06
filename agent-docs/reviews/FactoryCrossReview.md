# Mathematical cross-review of general factories

Reviewer: `prove_continuous`, independent of `prove_general_factories`.
This supplements `StructuredProofs.md`; no author files were edited.

## Rejection — accepted mathematically

Reviewed source SHA-256:
`a6f667c40bc8b6375ea16ac7067ab08608e84ea94e041efce7d75deaf378a055`.

The target `(μ s)⁻¹ • μ.restrict s` is the normalized conditional proposal law.
The main theorem requires measurable `s` and nonzero acceptance mass. Since `μ`
is a probability measure, this mass is finite; inverse cancellation is therefore
valid. The excluded zero-mass boundary is necessary. Acceptance mass one is
included without an artificial nonzero-rejection assumption.

The amplification choice `k = 1 + μ(s)` is sound: `k > 1` and
`μ(sᶜ) * k ≤ 1`. Thus the accepted contribution returns the conditional expectation,
and the rejected contribution carries the same expectation plus amplified
termination credit. The proof uses an inequality and explicit credit weakening;
it does not falsely claim equality for the unused termination slack.

The expectation argument is valid for arbitrary ENNReal continuation credits,
including infinity. Its only inverse cancellation concerns the finite positive
acceptance mass. It never converts continuation credits into real numbers.
The acceptance callback's pure total-WP specification establishes exactly the
membership Boolean; the proposal's `IsDistSpec` supplies the conditional draw
needed at every retry.

Independent evidence:

- `lake build SampLib.Samplers.Rejection` passed.
- `/tmp/factory-cross-audit.lean` proves acceptance of `univ` preserves the proposal law.
- `/tmp/rejection-infinite-audit.lean` checks half-mass conditioning on `true`
  produces `dirac true`, and that a continuation equal to infinity only outside
  the acceptance set has conditional credit zero.
- The spec's axiom audit contains only `propext`, `Classical.choice`, `Quot.sound`.
- `review_structured` independently checked a mass-one concrete caller and framing.

Nonblocking polish suggestion sent to the author: the factor comment could
mention `(1-a)(1+a) ≤ 1` explicitly, with `a = μ(s)`. The existing mathematics
already exhibits the correct argument and is readable.

## Probability-generating factory — accepted mathematically

Reviewed source SHA-256:
`5db3a3a5070f52cf6cb39fc52a4d58f57eac69aa9c1a99f4a2532baff7a4c66b`.

The target `ν.bind (IterateCoin.law p)` is the Bernoulli(`p^N`) mixture for
`N ∼ ν`. It is normalized for every probability measure `ν` on naturals and every
unit-interval `p`. No finite expected count is needed: each sampled natural count
is finite, and the finite-iteration specification supplies the conditional result.

The single expectation lemma is Tonelli/measure-bind conditioning. Its measurability
hypotheses are discharged by the countable input and output types. It accepts
arbitrary ENNReal credits, including infinity, without any boundedness or moment
assumption. The program proof uses the count specification, checks the natural
count's domain, and invokes the verified iteration specification. This faithfully
matches the implementation.

Independent `/tmp/factory-cross-audit.lean` proves:

- Exact true mass: `law ν p {true} = ∫⁻ n, ENNReal.ofReal ((p : ℝ)^n) ∂ν`.
- At `p = 0`, true mass is `ν {0}`; the `0^0 = 1` case is handled correctly.
- At `p = 1`, the full output law is `dirac true`.
- A point-mass count specializes to the corresponding `IterateCoin.law`.
- The public spec's axiom audit contains only the three standard Lean axioms.

An independent combined build of `SampLib.Samplers.Rejection` and
`SampLib.Samplers.ProbabilityGeneratingFactory` passed; the audit imported those
artifacts successfully. The target mixture is mathematically intelligible;
an optional direct success-mass lemma would make the PGF identity even more
immediate to a reader. This is a presentation suggestion, not a correctness gate.

## Logistic factory — accepted mathematically

Reviewed source SHA-256:
`65fb8fe358fbf5ce6f5214418b0f6eb4cb31018fdb7bc576a491a7d2a481a616`.

The public theorem covers all positive integer coefficients `x,y` and every
unit-interval input bias `p`. It invokes the actual verified rational selector,
not an unproved concrete-primitive assumption. The target `integerBias` is
explicitly `x*p/(y+x*p)`, with a positive denominator supplied by `y>0` and the
unit-interval proof supplied independently of the CTE argument.

The internal selector bias is `r=y/(x+y)`. Positivity of `x,y` establishes
`0<r<1`, so the internal strict selector domain loses no valid public inputs.
The retry probability is `q=(1-r)(1-p)`. The adopted amplification factor
`k=1/(1-r)>1` satisfies `q*k=1-p≤1`; it remains valid at both `p=0` and `p=1`.
In particular, no division by the actual retry probability excludes `p=1`.

The expectation lemma verifies the two scalar fixed-point equations
`q*b+(1-r)*p=b` and `q*(1-b)+r=1-b`, then factors the true, false, and auxiliary
credit contributions. All scalar transports involve finite probability
coefficients; arbitrary continuation credits stay in ENNReal. Thus the proof
also handles infinity on a null outcome. The inequality correctly retains any
unused termination-credit slack.

Independent evidence:

- `lake build SampLib.Samplers.LogisticFactory` passed.
- `/tmp/logistic-cross-audit.lean` proves input bias zero yields `dirac false`.
- At input bias one, output bias is `x/(x+y)`; it is correctly not forced to one.
- Unit coefficients give bias `p/(1+p)`.
- At input bias zero, credit infinite only on `true` has target expectation zero.
- The complete preservation lemma specializes to that null-infinite-credit case
  with zero budget, checking its handling through both selector and input draws.
- Public spec and preservation-lemma axiom audits contain only the three standard
  Lean axioms.

No blocking findings. The author addressed the clarity suggestion by displaying
`q+D=1` and using this shared balance in both scalar recurrences. Separate
sections now isolate distribution, termination, conservation, and program logic.
The final calculation clearly identifies which coefficient funds each
continuation and the auxiliary credit. Focused re-review confirmed that the main
CTE proof and public specification are unchanged, and final independent build and
endpoint/infinity/axiom checks passed. The structured reviewer separately checks
caller framing and presentation.

## Review scope

This review checks the mathematical specifications, expectation arguments, domain
boundaries, arbitrary-credit support, and consistency with the implementation.
The independent structured reviewer additionally checks proof style and callers.
Any source change after the hashes above requires a focused re-review.
