# Domain findings during the expansion campaign

## Unrestricted positive rational continued fractions

Source: `Occil.Constants.rationalContinuedFraction` in
`code/Samplers/Constants/Engines.lean` (lines 98–109).

An almost-sure total specification for every guard-valid infinite coefficient
sequence is false. At position `i ≥ 1`, let the coefficient callback return
`(1, (1, (2^i, false)))`. Thus `b_i = a_i = 1`, `d_i = 2^i`, and no entry is final.
Every runtime parameter check succeeds.

The first coin stops the descent with probability `1 / (1 + 2^i)`; otherwise the
program calls position `i + 1` before any possible return or retry. Along this
first descent,

```text
Σ_{i≥1} 1/(1+2^i) ≤ 1/3 + Σ_{i≥2} 2^(-i) = 5/6.
```

The union bound therefore leaves probability at least `1/6` of descending forever.
This event never returns from the initial call. The coefficient callback itself
is representable by a terminating integer-power computation.

This rejects the unrestricted guard-valid almost-sure specification. It does not
reject finite terminating continued fractions or infinite subclasses with proved
termination conditions. The integer engine `generalizedContinuedFraction` has
different progress bounds and remains a candidate.

Analytic finding by `expand_constants`, independently checked against the source
by root. This note records a domain counterexample, not a Lean nontermination
theorem or an accepted sampler proof.

## Low-probability linear wrapper

`Occil.FactoryExtra.linearLowProbability` advertises the domain
`μ = (a/b)p ≤ ρ = m/n < 1/2`. Its expanding branch calls
`Linear(a*n, b*2*m, n-m, n)`. That call's bias is `μ/(2ρ)`, while its supplied
margin requires that bias to be at most `ρ`. The advertised domain implies only
the weaker bound `μ/(2ρ) ≤ 1/2`.

For `a=2, b=1, m=1, n=4, p=1/8`, every advertised condition holds. The inner
call is `Linear(8,2,3,4)`, whose desired bias is `1/2` but whose certificate
demands a bias at most `1/4`. Replacing the domain by `μ ≤ 2ρ²` would silently
exclude valid inputs and is not an acceptable verification.

An exact finite-depth calculation strengthens the contract mismatch. Following
the actual Linear parameter updates reaches a desired bias `15/14` after six
recursive levels. Optimistically replacing every call there by `true` bounds
the real success probability from above: each intervening finite retry loop is
a polynomial with nonnegative coefficients in its recursive success probability.
The gambler and high-power walk probabilities are the already reviewed finite
geometric-sum formulas. Upward rounding after each level preserves the bound.

The [rational certificate](../../agent-scripts/check_low_probability_margin.py)
gives

```text
inner Linear success ≤ 1152918381151618905 / 2305843009213693952 < 1/2,
wrapper success ≤ 3458761390365312857 / 13835058055282163712 < 1/4.
```

The wrapper's outer logistic success probability is `1/3`, followed by a fair
choice between immediate success and the inner call, giving the second bound.
The certificate uses exact fractions, not sampled executions. This is analytic
source-rejection evidence, not a Lean theorem about the defective program.
The factory reviewer independently checked the source recurrence, positivity and
monotonicity of each walk polynomial, all seven parameter tuples, the optimistic
cutoff, and the upward rational rounding, and reproduced the strict bound. The
runtime source remains unchanged.
