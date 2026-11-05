# ProbLang extensions for the Occil sampler corpus

Audit target: `logsem/clutch-lean` main, commit
`54e780e43709d2f28386b83bffccdde498141b25` (Lean 4.35.0).
This is a wishlist, not a proposal to modify or publish the private/public repositories now.

## Decision

Proceed with the substantial existing-language subset first. Integer arithmetic, recursive
functions, products/sums, mutable heaps/arrays, uniform integers/reals, real addition,
negation, comparisons, rational constants, integer-to-real conversion, and fractional
parts already support many samplers. In particular, real multiplication and transcendental
operations are NOT required for von Neumann exponential sampling or Karney-style Gaussian
sampling. Generic terms can run at `Float` and later be specified at `ℝ`.

Real arithmetic is nevertheless a broad limitation, affecting ordinary scale/location
families, geometric sampling, and standard normal/gamma/beta algorithms, not just exotic
samplers. Collect these extensions into one upstream pass when expanding that coverage.

Update: `Samplers.Lazy` now implements memoized binary uniform streams, exact
rational comparisons, geometric-bag sampling, and factorial-series Bernoulli
factories for exponential, sine and cosine probabilities. Logarithm/arctangent
coin factories use integral mixtures. These do not need numerical transcendental
primitives. General PSRN arithmetic and real-valued transcendental transforms
remain separate work. `Samplers.More` adds integer alias preprocessing and
Bernstein-polynomial factories; these also require no upstream changes.

## Priority 1: real arithmetic and numerical observations

| Feature | Algorithms unlocked | Semantics and verification requirements |
| --- | --- | --- |
| Real multiplication | Affine scaling, triangular transforms, geometric rejection, multivariate transforms | `ProbLangℝ` operation, lawful real instance, measurable semantics, typing and CTE pure-step rules, Float interpreter |
| Real subtraction | Most numerical pseudocode | Can be surface sugar for addition and negation; a new AST operation is unnecessary |
| Real division/reciprocal | Arbitrary-rate exponential, gamma/beta ratios, Cauchy, normalized vectors | Choose total field convention versus stuck on zero explicitly; prove guarded-domain specifications |
| Real powers with integer exponent | Polynomial densities, rejection envelopes, moments | Can be a verified library term once multiplication exists; negative powers require nonzero guards |
| Real-to-integer floor/ceiling | Integer/fraction decompositions, inversion, rounded outputs, bounded geometric methods | Integer-valued results, measurability at discontinuities, exact-real laws, explicit nonfinite Float behavior; `frac` alone does not return the integer part |
| Endpoint-safe uniform interface | Logarithmic transforms and rejection methods | Current IO draws include 0 and exclude 1, whereas the mathematical real instance is concentrated on `(0,1)`; provide an open-interval runtime draw or a verified redraw wrapper |

## Priority 2: elementary mathematics

| Feature | Algorithms unlocked | Notes |
| --- | --- | --- |
| Natural log and `log1p` | Inverse exponential, polar/ratio-of-uniforms normal, gamma, stable, Weibull/Pareto/logistic transforms | `log1p` needs an accuracy contract beyond ideal-real equivalence; specify domains |
| Square root | Normal polar/Box–Muller, geometric normalization, gamma methods | Specify nonnegative input; can also be a validated approximation library |
| Exponential and `expm1` | Lognormal, rejection densities, stable numerical transforms | Separate ideal values from Float overflow/underflow and accuracy |
| Sine/cosine, tangent | Box–Muller, stable and von Mises samplers, Cauchy, sphere coordinates | Prefer common argument reduction/backend; tangent needs pole guards |
| Arctangent, inverse cosine/sine | Inverse-CDF and directional samplers | Domain/range contracts |
| Real power | Weibull, gamma/beta methods, stable and exponential-power distributions | Positive-base version first; exponent-zero and zero-base conventions |
| Pi and other named computable constants | Angles, Cauchy, normal and stable transforms | `realOfRat` already supplies rational constants; do not pretend a rounded literal is exact pi |

Derived hyperbolic functions and inverse functions can be library definitions after these
operations. Constant approximation may instead use constructive reals or certified intervals.
No need to add a primitive for every distribution transformation.

## Priority 3: extensibility, avoiding repeated syntax changes

A registered deterministic numerical-function interface could cover elementary functions,
`erf`/normal CDF and quantiles, log-gamma, incomplete gamma/beta, and user CDF/PDF/quantile
functions. Require each registration to supply argument/result shapes, measurable ideal
meaning, domains, CTE rules, and a runtime implementation. Many inverse-transform examples
are best stated parametrically over a verified quantile callback.

Existing `ffi`, `ProbLangFFI.ofCode`, named `sample`/`test`, and `ProbLangDist` already provide
semantic extension points. Audit/reuse them before adding AST constructors. The current IO
environment interpreter rejects FFI calls, tests, and non-uniform named distributions;
semantic extensibility alone does not make these programs executable. Do not implement a
sampler by registering the target distribution itself: that would bypass its algorithm.

## Priority 4: exact/lazy numbers (mostly library and proof infrastructure)

- Rational arithmetic: normalized integer pairs, exact comparisons, safe division and
  conversion. Existing arbitrary-precision integers suffice for a library implementation.
- PSRN representation: base, sign, integer part, optional cached digits, including non-prefix
  digit access. Preserve already sampled digits and shared identity across comparisons.
- Uniform/exponential conditional-tail invariants and a coupling to the represented real.
- Comparison refinement, arithmetic interval refinement, dyadic ambiguity/null-event lemmas,
  and almost-sure termination of each requested observation. Equality of shared values
  needs explicit handling; comparisons need not terminate for arbitrary equal constructive reals.
- Precision/rounding requests with absolute or relative error and an explicit rounding rule.
  A finite machine return is not the same object as an ideal continuous output.
- Geometric bags, order statistics, lazy transformations, and constructive transcendental
  arithmetic. These unlock the PSRN beta/exponential families and their many derivatives.

Pairs/sums, recursion and heap allocation already support list/vector/tree encodings and
memoization. Matrix algorithms, sorting, heaps, alias tables, reservoir state, and automatic
discrete-code generation primarily need libraries, not language primitives. Array support
already exists; convenience syntax and reusable separation-logic lemmas would help.

## Priority 5: interpreter and experiment support

- Configurable per-run fuel/step budget; distinguish budget exhaustion, stuck programs,
  nonfinite numerical output, and ordinary return. A process timeout is only a fallback.
- Injectable seeded random source and a replayable random-draw trace; IO.setRandSeed already
  permits seeded experiments. Count integer draws, bits, uniform draws, steps and heap use.
- Runtime handlers for registered FFI/named distributions and observations, with differential
  tests against the substitution evaluator and the semantic specification.
- Exact float serialization (IEEE bits), structured result values, and streaming batches.
- Retain finite-precision qualifications: IEEE Float is explicitly not a lawful real model;
  statistical agreement is implementation evidence, not an exact-real soundness theorem.
- Independence/joint-law tests for multiple outputs and shared cached variates; support,
  endpoints, parameter boundaries, tails, and invalid-input tests as well as mean/variance.

## Proof support to request with any extension

Every numeric extension needs the real interface and lawful real instance, measurable
small-step semantics, pure-step reductions and CTE rules, typing, evaluation-context and
readback support, and executable interpreter behavior. Audit any affected contextual
refinement and erasure lemmas. Partial domains and IEEE exceptions must be intentional.

Reusable CTE rules for rejection/restart, mixture/composition, finite loops, probabilistic
recursion and adaptive digit revelation should accompany the sampler library. Prove full
output measures and almost-sure termination; expected cost needs additional arguments.
MCMC stationarity and convergence do not imply exact finite-time sampling; coupling from
the past needs its own coalescence and termination hypotheses.

## Frontend ergonomics (not blockers)

The current surface grammar gives `&&`/`||` higher precedence than comparisons,
so compound guards must write `(x < y) || (z < w)` explicitly. Conditional and
recursive expressions used as local `let` right-hand sides also need parentheses
to delimit their bodies before the separating semicolon. Consider conventional
precedences and clearer parser errors in a future frontend pass; the current
samplers already use the required parentheses. These changes need no semantic
extensions, but should preserve existing parsed terms or be introduced deliberately.

## Corpus references

- https://peteroupc.github.io/randomfunc.html
- https://peteroupc.github.io/randomnotes.html
- https://peteroupc.github.io/bernoulli.html
- https://peteroupc.github.io/bernsupp.html
- https://peteroupc.github.io/exporand.html
- https://peteroupc.github.io/randmisc.html
- https://peteroupc.github.io/bernapprox.html

Scope covers the sampler corpus, including alternatives and supporting numerical methods.
It does not include implementing PRNGs, a general-purpose special-functions library, or
settling the site's open research questions. Further source defects should be recorded
explicitly rather than silently incorporated into a purported literal translation.
