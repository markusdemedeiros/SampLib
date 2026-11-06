# Domains of lazy-real observations

Finite interval observations and later numerical decisions have different termination domains.
The deferred-law protocol proves that each requested interval is returned, contains the same latent
real, and shrinks. It does not by itself prove termination of `less`, `floorScaled`, or a root's
internal comparisons.

- `less left right` terminates almost surely when their represented values are unequal almost
  surely and the measurable interval errors vanish. Shared or identical operands must retain
  their joint law. A scalar marginal hypothesis cannot establish this condition.
- `floorScaled source scale` needs almost-sure avoidance of the grid boundaries, or a separate
  certificate that this particular oracle resolves its boundary atoms. Positivity and shrinking
  width alone are insufficient.
- `root` calls `less` against rational powers of its successive bisection bounds. Almost-sure
  avoidance of these comparison boundaries suffices. Exact or one-sided representations may
  admit more atoms, but each such extension needs its own proof.
- `expMinusCoin` starts with `floorScaled source 1`. Its domain must include this observation
  obligation as well as nonnegativity; it cannot silently inherit all nonnegative latent values.

Concrete example: `newByDigits` with an always-true digit callback represents the value `1` using
intervals `[1-2^(-n),1]`. At scale `1`, the lower and upper integer quotients remain `0` and `1`,
so `floorScaled` keeps refining. This is an implementation/domain observation, not yet a Lean
counterexample theorem. An exact rational oracle for `1` returns the point interval `[1,1]` and
resolves immediately. The represented measure alone therefore does not determine observability.

Continuous uniform/gamma/normal constructions avoid countable grid and rational-power boundaries
almost surely when their actual latent laws are proved non-atomic. Posterior absolute continuity
preserves those facts after cached observations. Constant and mixture branches need explicit
representation-aware treatment.

Keep these obligations in the public domains and caller fixtures. Do not weaken the existing
finite-observation protocol, assume unavailable probability-zero facts, or replace an actual
sampler's interval oracle to make its proof easier.
