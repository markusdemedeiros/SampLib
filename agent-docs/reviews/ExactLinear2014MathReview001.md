# Linear 2014 mathematics: independent design review

Reviewer: `/root`. This reviews the five pure mathematical modules below;
`review_exact_a` retains responsibility for concrete symbolic execution, nested
error-credit induction, public domains, callers and final sampler acceptance.

The stage parameters encode `c=a/b>1`, target `t=cp<=1-epsilon`, geometric
success `q=(c-1)/c`, and a positive rational boundary N/D with
`2D<=epsilon*N`. The identity `(1-q)t=p` is deliberately division-free in `t`.
The geometric generating function is `q/(1-(1-q)t)` with a strictly positive
denominator. It makes the next-state mixture (true: s-1; false: s+G) preserve
the Boolean expectation with true mass `t^s`. The proof covers `p=t=0`, never
requiring a positive input probability or a finite continuation expectation.

Within one fixed stage, a false trial followed by at least N geometric failures
escapes every ordinary state (D>=1). Its positive mass
`Delta=(1-p)(1-q)^N` bounds ordinary continuation probability by `1-Delta`.
This is conservative but sufficient: multiplication by `1+Delta>1` funds the
inner error-credit induction since `(1-Delta)(1+Delta)<=1`. The state-law module
is a normalized dirac/map mixture and identifies exactly this source transition.

At a boundary, beta=1+epsilon/2 changes t to beta*t, halves epsilon and doubles
the threshold. The admissibility inequality is preserved because
`(1-epsilon)(1+epsilon/2)<=1-epsilon/2`. The selector probability beta^(-n)
cancels the boosted power exactly, returning false otherwise. Boundary crossing
implies n*epsilon>=2; Bernoulli's inequality gives beta^(-n)<=1/2 and therefore
funds doubled outer termination slack. This avoids an unnecessary global
overshoot estimate or a uniform escape constant across all stages.

`Parameters.expectation` combines the output harmonic credit, outer slack and
inner ordinary-state slack in one inequality. State zero returns true, ordinary
states recurse within the stage, and boundary states use the selector estimate.
All integrations of arbitrary continuation credits remain in ENNReal; only
bounded scalar probabilities and finite amplification constants use reals.
No subtraction of infinite credits or continuity at zero times infinity occurs.

The initial threshold 23/(5epsilon) satisfies the weaker invariant used above.
Both branches of the source's margin clamp are preserved; clamping to 644/1000
weakens the original bound. The positive integer/domain assumptions establish
all denominators and cast transitions explicitly.

No correctness or mathematical presentation revisions requested. Inspected hashes:

- `SampLib/Distributions/Linear2014Jump.lean`: `5374e4b854d533aed0c326bc446dd35588577a6e55f50ded914bb709260f3a20`
- `SampLib/Distributions/Linear2014Escape.lean`: `6a8a0f17dc11de32955a9220ad153e8e4ba56e782c49a6564729f4abc56bb7be`
- `SampLib/Distributions/Linear2014Step.lean`: `0c0f3261d68a00a2850049ece32d023f31c5979f2552518e727868b332ea50ec`
- `SampLib/Distributions/Linear2014Credit.lean`: `f6599676b75c4874b2332cd5cc6545ab7fb80a53e2020adb1d06292d21ea7be5`
- `SampLib/Distributions/Linear2014Parameters.lean`: `eba5c38c6c038c4cf26beae585cce2e90e19f6571f98627b038ddd9b49aa95ba`
