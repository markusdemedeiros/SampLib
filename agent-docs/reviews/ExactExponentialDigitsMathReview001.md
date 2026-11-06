# Exponential digit mathematics: independent design review

Reviewer: `/root`. Supporting mathematical design pass only. The concrete digit
reader, decay/retry program, geometric integer-part source, constructor ownership
and final sampler acceptance remain with their authors and `review_exact_b`.

The fractional law is the exponential density restricted to `[0,1)`, divided by
`1-exp(-rate)>0`. Its normalization follows from the elementary antiderivative;
absolute continuity supplies endpoint nullity and atomlessness. Every nonempty
dyadic cell has positive mass for every positive real rate.

Exponential translation invariance makes the upper half's mass a fixed logistic
fraction `1/(1+exp(rate*width/2))` of the parent mass. The cross-multiplied
`half_mass` identity exposes the argument before normalization, avoiding division
by a tiny interval mass. Conditioning cancels only a positive finite cell mass.
The decay form `exp(-rate*width/2)/(1+exp(-rate*width/2))` matches the source's
fair/decay retry experiment, with width `2^(-prefix.length)`.

Canonical digits use the terminating expansion at dyadic rationals. Their series
value equals the represented real on `[0,1)`. To identify prefix cylinders, the
argument sandwiches any stream value in its prefix's dyadic interval, then uses
integer rank separation to identify the prefix at strict interior points. The
two boundary points are null under the absolutely continuous fractional law.
Consequently the actual memoized `DigitPosterior.nextLaw` is the advertised
Bernoulli law at every finite prefix, not merely an unconditional digit marginal.
The pushforward by the represented digit value is exactly the fractional law.

For the whole part, geometric stopping probability `1-exp(-rate)` gives mass
`exp(-rate)^n*(1-exp(-rate))`. Multiplying by the fractional density cancels the
normalizer and yields the original exponential density on the n-th unit strip.
The proved ENNReal expectation identity sums these translated strips over the
nonnegative half-line. It accepts arbitrary measurable credits, including
infinite credits, without signed subtraction or a finite-expectation assumption.
The whole and fractional draws must remain independent in the concrete source
constructor, while all repeated reads of the resulting oracle share one world.

No mathematical correctness or presentation revisions requested. The rate-zero
case is deliberately excluded from the normalized construction; binary endpoints
are treated by exact canonical representation or explicit nullity as appropriate.
Inspected hashes:

- `SampLib/Distributions/ExponentialDigits.lean`: `fe79089ce7f2e96120657c9342ed02053e196073e1a7e255749042628fdc8f63`
- `SampLib/Distributions/ExponentialWholeFraction.lean`: `1fcfed874ea6da1dc2be0f855b35c264d01e8050a370e34296cc14c99316230e`
- `SampLib/Distributions/ExponentialDigitCells.lean`: `0fb3465029b4e94f50825c9a8072d9263a159e1ffd69bc745aa9933ff5a0352e`
- `SampLib/Distributions/ExponentialDigitLaw.lean`: `644f16692b11a4676d3f7e936ebb9a3011e12a06b39eb2453f7efa955cac0137`
