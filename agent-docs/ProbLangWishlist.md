# ProbLang extensions for the remaining Occil samplers

Audited on 2026-11-06 against the installed `logsem/clutch-lean` dependency,
commit `54e780e43709d2f28386b83bffccdde498141b25`, using Lean 4.35.0.
The installed package is `.lake/packages/clutch-lean`; the leftover
`.lake/packages/metrology` checkout is stale.

## Requested upstream batch

Add real multiplication/division, real-to-integer floor, and an executable
registered interface for deterministic mathematical functions. Include the
semantic, typing, CTE and interpreter support in the same update. These enable
ideal-real versions of the large numerical branch and simplify their proofs.

The current corpus already implements those numerical methods with integer
fixed-point arithmetic. Its PSRN algorithms also already execute using integer
interval oracles. New primitives do not change the laws of those existing terms.

The catalogue has 588 sampler entries and 216 accepted standalone sampler specs.
The other 372 entries split as follows:

| Remaining catalogue entries | Count | Main work |
| --- | ---: | --- |
| Exact factories, constants, discrete, general and weighted methods | 99 | Mathematical and CTE library proofs |
| Lazy exact reals and coins | 49 | Owned latent-real representations and refinement proofs |
| Numerical/grid algorithms | 224 | Numerical specifications, or separate ideal-real implementations |

These are catalogue gaps: some entries, including `sampleGeometricBag` and
`voseDraw`, already have supporting proofs inside larger verified techniques.
The implemented-entry list is in [LAWS.md](../LAWS.md). These counts do not
establish exhaustive coverage of every algorithm in Occil's articles.

## Bernoulli factory coverage

The catalogue contains 93 ordinary factory terms (60 accepted specifications)
and eight lazy-coin terms (five accepted standalone specifications). Constant
coins have a separate category. The remaining ordinary 33 include the known
incorrect `linearLowProbability` wrapper, so this is not a list of 33 valid
targets awaiting routine proofs.

Source coverage also needs work beyond this implemented-term catalogue:

- Occil's Dice Enterprise construction builds a polynomial ladder and uses
  monotone coupling from the past to sample multiple polynomial-ratio outcomes.
  Our `rationalFunction` uses a two-polynomial Bernoulli race; the general CFTP
  engine does not itself supply the missing polynomial-to-ladder construction.
- The general envelope engine currently takes valid coefficient bounds through
  callbacks. Automatic construction of those envelopes from function regularity
  data is separate implementation and proof work.
- The supplemental efficient multiple-output construction uses randomness
  extraction and recycling. Repeating an existing factory supplies multiple
  samples but does not implement that efficiency-oriented algorithm.

See [the rational-function constructions](https://peteroupc.github.io/bernoulli.html#certain-rational-functions)
and [multiple-output factories](https://peteroupc.github.io/bernsupp.html#multiple-output-bernoulli-factory).
These concrete gaps primarily need integer/coin algorithms and mathematical
proofs. Native real transcendental functions are not prerequisites for them.

## Priority 1: real arithmetic and observations

| Request | Concrete interface change | Coverage |
| --- | --- | --- |
| Real multiplication | Add `ProbLangℝ.realMul`, its measurability law, and real cases for existing `BinOp.mult` | Affine scales, polynomial rejection, covariance transforms, geometric constructions |
| Real division | Add `ProbLangℝ.realDiv`, its measurability law, and real cases for existing `BinOp.div` | Gamma/beta ratios, Cauchy, normalization, arbitrary-rate transforms |
| Real subtraction | Handle real operands for existing `BinOp.minus`, using addition and negation | Ordinary location/scale formulas; no separate real-subtraction field needed |
| Floor returning an integer | `realFloor : T → Int` through unary syntax or a typed registry entry; measurability and the ℝ floor equation | Integer/fraction decompositions, discrete transforms and rounded observations |

The existing real interface supplies addition, negation, comparisons, integer
and rational conversion, and fractional part. The existing integer `*` and `/`
operators do **not** accept real operands. Mixed integer/real operations should
continue to use explicit coercions. `realFrac` cannot return the integer part.

Use Mathlib's total real division convention for the ℝ backend, with the usual
nonzero hypotheses in sampler proofs. Specify Float division-by-zero and
nonfinite outcomes separately. Ceiling, absolute value, min/max, integer powers
and standard rounding modes can be library terms after these operations exist.

Evidence: [real interface](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/Syntax/Syntax.lean#L127),
[binary evaluation](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/Syntax/Syntax.lean#L1225),
[real typing](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/Syntax/Types.lean#L137).

## Priority 1: deterministic elementary mathematics

Provide a registry with these initial entries:

| Entry | Ideal domain | Representative algorithms |
| --- | --- | --- |
| `log` | Positive argument | Inverse exponential, polar normal, gamma, stable and logistic transforms |
| `sqrt` | Nonnegative argument | Polar/Box–Muller normal, gamma methods, geometry |
| `exp` | All real arguments | Lognormal, densities and rejection envelopes |
| `sin`, `cos`, `atan` | All real arguments | Box–Muller, Cauchy, stable and directional methods |
| `pi` | Nullary constant | Angular and directional constructions |
| Positive-base real power | Positive base, real exponent | Weibull, beta/gamma transformations, stable families |

Real power can initially be a library definition using `exp (y * log x)`.
Specify the zero-base cases explicitly: `0^0 = 1`, positive powers of zero are
zero, and negative powers of zero are outside the guarded domain. Tangent,
inverse sine/cosine and hyperbolic functions can be derived or registered later.
The ℝ meaning of `pi` must be `Real.pi`; its Float implementation is an
approximation, rather than an exact rational literal.

### Reuse the existing FFI syntax and semantics

`ffi` and `ProbLangFFI.ofCode` already support registered code handles and a
measurable partial map on an argument and heap. A deterministic numeric entry
can return `FFIOutcome.ret` while preserving the heap.

The execution paths currently reject FFI:

- `EnvStep.StepOps` has no FFI operation; `resumeK` hardcodes a stuck result.
- The substitution reference evaluator also hardcodes FFI failure.
- Both `BigStepIO` execution modes need the executable handler.

Updating only an IO wrapper would leave the machines inconsistent. A registration
should supply argument/result shapes, its measurable ideal function, a valid
domain, an exact ℝ interpretation, a deterministic unchanged-heap step equation,
an executable backend and a reusable pure-step/CTE rule. Invalid domains must
have a stated failure or totalization policy. Keep registration IDs stable.

Use this interface for elementary and special functions while retaining the
sampler's random choices and control flow in ProbLang. Registering a completed
target distribution would bypass the algorithm we want to verify.

Evidence: [FFI registration](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/FFI.lean#L119),
[machine operations](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/EnvStep.lean#L80),
[environment rejection](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/EnvStep.lean#L322),
[reference rejection](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/BigStep.lean#L162).

## Priority 2: accuracy-oriented and special-function entries

`log1p`, `expm1`, `sincos`, `atan2`, `hypot` and power-of-two scaling are useful
backend operations for accuracy and range handling. Their stable Float contracts
are additional to their mathematical identities. `realScaleB : T → Int → T`
would help here, although its ideal meaning is derivable from real arithmetic.

The same registry can later supply normal CDF/quantiles, log-gamma, incomplete
gamma/beta and inverse functions. Generic quantile callbacks already express
many sampler interfaces; each concrete implementation still needs its proof.
There is no need for an AST constructor for every special function.

Keep IEEE bit operations, `frexp`, adjacent-float operations and directed rounding
in a separately specified floating-point interface. Integer bitwise and/or/xor
would accelerate packed-weight algorithms; existing integer arithmetic and
shifts already suffice to implement them. Current negative shift counts become
zero through `Int.toNat`; retain or deliberately revise that documented behavior.

## Numerical laws need a separate specification decision

[Numeric.lean](../code/Samplers/Numeric.lean) already implements multiplication,
division, roots, logs, exponentials and trigonometry inside the object language.
It uses unbounded integer fixed-point arithmetic, 24 guard bits, constants fixed
to 36 decimal places and an approximate normal CDF. These are executable algorithms, not
certified interval primitives. Increasing the grid scale does not remove every
analytic approximation error.

For the 224 numerical entries, choose the appropriate target per algorithm:

- The exact law of the existing integer/grid program.
- An error bound or rounding coupling to an intended continuous law.
- A separate ideal-real version using the new primitives, with its exact law.

CDF or Wasserstein bounds and rounding couplings are useful comparisons. A
finite-grid law and an atomless continuous law have total-variation distance
one, so a small raw total-variation claim would be inappropriate. Fixed-order
CLT normal approximations also retain approximation error at arbitrarily fine
grid resolution. Preserve the existing numerical terms when adding ideal ones.

`Float` is explicitly a lawless execution backend. Exact-real soundness and
Float error analysis are separate claims; statistical agreement checks execution.

## Project proof-library work: PSRNs and weighted methods

The remaining lazy 49 comprise 46 PSRN sampler entries and three lazy-coin
entries. PSRN already has 71 definitions including support: cached uniforms,
arithmetic, roots, rational powers, exponentials, Gaussian, beta/gamma, geometry
and transformed distributions. See [PSRN](../code/Samplers/PSRN.lean) and its
[arithmetic](../code/Samplers/PSRN/Arithmetic.lean).

The high-leverage proof interface is an owned latent-real oracle contract:

- Preserve cache ownership, the same latent value and its posterior credits
  when a caller requests a tighter rational interval.
- Support arbitrary ENNReal continuations and joint latent laws. Aliased
  operands such as `multiply x x` share randomness and exclusive resources.
- Compose interval arithmetic and refinement until separation, with explicit
  almost-sure boundary/nonzero hypotheses for comparisons and division.
- Specify returned oracles observationally, carrying their genuine heap state.

Generalize [UniformBag.IsCoinSpec](../SampLib/UniformBagCoin.lean) and reuse
[IsOwnedDistSpec](../SampLib/OwnedDistSpec.lean). Constructor, read, transform and
observation rules belong in the project logic library. A total comparison of
arbitrary constructive reals is not an implementable general primitive: current
`PSRN.less` can diverge on a shared nondegenerate oracle compared with itself.

Knuth–Yao, FLDR, Han–Hoshi, cyclic optimal matrices, inclusion samplers and packed
choices likewise need discrete probability/entropy proofs and heap invariants.
Persistent entropy recycling needs a posterior invariant for its retained pool;
a known pool state does not give an unconditional uniform next-output law.
[BitRecycler](../SampLib/Distributions/BitRecycler.lean) provides initial support.
Existing lists, arrays, heaps, recursion, integers and bits suffice for this work.

Known source-law defects also need domain review or algorithm repairs, rather
than new primitives: see [domain findings](reviews/ExpansionDomainFindings.md).

## Interpreter and proof-frontend improvements

| Request | Purpose |
| --- | --- |
| Per-run fuel and structured completion/stuck/budget/nonfinite results | Diagnose slow refinement and invalid numerical inputs |
| Injectable RNG, replayable draws and bit/step/allocation counters | Reproducible tests, entropy and runtime studies; global `IO.setRandSeed` already exists |
| Retained-state execution or observation callbacks | Observe returned PSRN closures before their heap is discarded; observing inside the object program already works |
| Handlers for existing non-uniform named samples and tests | Complete the existing interpreter extension points; keep numerical functions deterministic |
| Preserve named lambda/fix bodies in pure-step automation | Avoid expensive whole-source normalization and repeated local-closedness checks |
| Explicit diagnostics for unresolved expression/type parameters | Prevent misleading closedness recursion/heartbeat failures |

IEEE Float hex serialization and streaming batches already exist in
[Interp/Sample.lean](https://github.com/logsem/clutch-lean/blob/54e780e43709d2f28386b83bffccdde498141b25/Metrology/ProbLang/Interp/Sample.lean).
They are not missing features. Current runtime uniforms include zero and exclude
one. An open-interval redraw wrapper can protect logs and reciprocals while
retaining the explicit finite-grid runtime interpretation.

[BetaStep](../SampLib/BetaStep.lean) and checked source-opening caches already
solve our large-lambda proof issue. Upstream automation could absorb this
idiom; it requires no semantic extension. See the
[proof-transport notes](LatentUniformProofs.md#keeping-syntax-transport-out-of-symbolic-execution).

The current parser requires parenthesized comparison operands in compound
`&&`/`||` guards and parentheses around conditional/recursive `let` RHSs.
Conventional precedences and clearer diagnostics are optional ergonomic work;
preserve existing parsed programs. Automatic type checking is also partial,
including some real syntax; extend it alongside semantic typing where practical.

## Definition of done for the upstream update

Ship the real data interface and ℝ instance; measurable evaluation; typing;
concrete ℝ reduction equations; generic pure-step/CTE support; both interpreter
paths; executable handlers; and domain/endpoint/differential tests. Exercise
zero denominators, negative floor inputs, log/sqrt domains, nonfinite Float
results and the uniform endpoint convention. Check closure/context/readback
lemmas affected by new syntax and preserve existing integer programs.

After updating this project's dependency, rebuild the existing 216-spec suite
and replay its callers. Review receipts pin dependency/context hashes, so issue
new immutable migration evidence for the new context while retaining the old
receipts and frozen baseline audit. A successful build alone does not refresh
those records. Keep Float approximation claims explicit when adding ideal terms.
