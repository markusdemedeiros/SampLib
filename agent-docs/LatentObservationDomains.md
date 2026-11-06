# Domains of lazy-real observations

A finite interval observation and a later numerical decision have different termination
domains. The deferred-law protocol proves that each requested interval comes back,
contains the same latent real, and shrinks. That protocol alone does not prove that
`less`, `floorScaled`, or the internal comparisons of a root terminate.

- `less left right` terminates almost surely when the represented values of its operands
  are unequal almost surely and the measurable interval errors vanish. Shared or identical
  operands must keep their joint law. A hypothesis about scalar marginals cannot establish
  this condition.
- `floorScaled source scale` needs the source to avoid the grid boundaries almost surely,
  or a separate certificate that this particular oracle resolves its boundary atoms.
  Positivity and shrinking width alone are not enough.
- `root` calls `less` against rational powers of its successive bisection bounds. It is
  enough to avoid these comparison boundaries almost surely. Exact or one-sided
  representations might admit more atoms, but each such extension needs its own proof.
- `expMinusCoin` starts with `floorScaled source 1`. Its domain must include this
  observation obligation as well as nonnegativity. It cannot silently inherit every
  nonnegative latent value.

For example, take `newByDigits` with a digit callback that always returns true. It
represents the value `1` with the intervals `[1-2^(-n),1]`. At scale `1`, the lower and
upper integer quotients stay `0` and `1`, so `floorScaled` keeps refining. This finding
describes the implementation and its domain; no Lean theorem states it as a
counterexample yet. An exact rational oracle for `1` returns the point interval `[1,1]`
and resolves at once. So the represented measure alone does not decide observability.

Continuous uniform, gamma, and normal constructions avoid countable grid boundaries and
rational-power boundaries almost surely, once a proof shows that their actual latent laws
are non-atomic. Absolute continuity of the posterior preserves these facts after cached
observations. Constant and mixture branches need explicit, representation-aware
treatment.

Keep these obligations in the public domains and in the caller fixtures. Do not weaken the
existing finite-observation protocol. Do not assume probability-zero facts that are not
available. Do not replace the interval oracle of an actual sampler to make its proof
easier.
