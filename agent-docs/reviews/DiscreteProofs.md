# Independent review: uniform and discrete sampler proofs

Reviewer: `review_discrete`. Authors: `prove_uniform`, `prove_finite_trials`,
`prove_infinite_counts`. Existing `realCoin` and von Neumann proofs are baselines,
not new sampler counts.

A sampler is accepted only after source/specification review, an independent
module build, transitive axiom inspection, and a meaningful client/endpoint check.
All target laws must be normalized mathematical laws, not execution measures.

## Current verdicts

| Sampler | Verdict | Evidence and outstanding work |
| --- | --- | --- |
| `iterateCoin` | **Accepted** | Independent build, resource-preserving client, all three boundary checks, and axiom audit passed. |
| `uniformInt` | **Accepted** | Independent build, singleton bound, resource-preserving client, and axiom audit passed; normalization/cast polish resolved. |
| `rndInt` | **Accepted** | Independent build, zero-bound law, framed caller, and axiom audit passed. |
| `rndIntRange` | **Accepted** | Independent build, arbitrary signed singleton law, framed caller, and axiom audit passed. |
| `rndIntExcRange` | **Accepted** | Independent build, negative width-one law, framed caller, and axiom audit passed. |
| `fairCoin` | **Accepted** | Independent build, framed caller and composition with IterateCoin, and axiom audit passed; pure cast helper/core wrapper polish resolved. |
| `rationalCoin` | **Accepted** | Independent build, full rational endpoint checks, framed caller, actual RationalCoin→VonNeumann composition, and axiom audit passed; scope polish resolved. |
| `boundedGeometric` | **Accepted** | Independent build, p=0/p=1 law checks, resource-preserving client, and axiom audit passed. |
| `binomial` | **Accepted** | Independent build, p=0/p=1 law checks, framed caller, and axiom audit passed. |
| `randomWalk` | **Accepted** | Independent build, n=0 and one-step mass checks, framed caller, and axiom audit passed. |
| `geometric` | **Accepted** | Canonical-law source review, independent source build, p1 atom checks, framed caller, FairCoin composition, and axiom audit passed. |
| `negativeBinomial` | **Accepted** | Independent build, zero-success/p1 laws, full-domain framed caller, actual FairCoin composition, and axiom audit passed. |

## Review findings

### `iterateCoin`

Reviewed file SHA256: `f14b4ee475b3ea318aef1a1c2705d6a687818886abb00b533690629d3478bbfe`.

- Matches the actual recursive all-successes algorithm in `Samplers.Continuous`.
- Domain is every natural `n` and every unit-interval input bias, including `n=0`,
  `p=0`, and `p=1`. No unnecessary primitive randomness assumption is introduced.
- Canonical target is Bernoulli(`p^n`), using the existing normalized Boolean law.
- The expectation lemma accepts arbitrary ENNReal credits, including infinity;
  local real/ENNReal coefficient equalities concern only finite probabilities.
- Program logic uses finite induction, one abstract callback call per iteration,
  explicit Boolean branches, and no embedded mathematical search.
- Independent build: `lake build SampLib.Samplers.IterateCoin` passed.
- Axiom checks for the core theorem, public spec, and expectation lemma contain
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Public theorem: `SampLib.IterateCoin.iterateCoin_distSpec E p coin hcoin n`.
  Input is `IsDistSpec E (coin ()) (RealCoin.law p) Val.bool`; output is
  `IsDistSpec E (Occil.iterateCoin coin n) (IterateCoin.law p n) Val.bool`.
- Independent client/axiom command:
  `lake env lean /tmp/samplib-review-discrete/IterateAudit.lean` passed. The client
  calls only the public spec through `IsDistSpec.wp` and retains arbitrary
  `I : IProp GF` in the postcondition. Checks prove `bias p 0 = 1`,
  `bias 0 (n+1) = 0`, and `bias 1 n = 1`.
- No corrective change was needed. The exposed recurrence has a clear success
  factorization and treats only finite coefficients as reals.

### `uniformInt`

- Domain and intended output agree: positive exclusive natural bound, uniform
  position law on `0,…,n-1`, encoded as object-language integers.
- The typed spec uses the mathematical finite-uniform law rather than operational
  executions; its expectation accepts arbitrary natural-indexed ENNReal credits.
- Suggested replacing the hand-written probability-normalization proof with
  installed `Measure.isProbabilityMeasure_uniformOfFinset`. Sent to author.

## Pending mathematical checks

The finite-trial author and root agree that explicit normalized convolution laws
are acceptable targets for binomial counts, capped geometric failures, and
symmetric random walks. These must remain recognizable independent-trial laws
with complete natural count and terminating coin endpoint domains. A closed-form
PMF appendix is not a prerequisite; an operationally recursive definition of the
execution distribution would be rejected.

### `boundedGeometric`

Reviewed file SHA256: `9d38721aa9012b9cd8b33d661ad269d27f3db932df02c266d7cffbced5496ab8`.

- Public theorem: `SampLib.BoundedGeometric.boundedGeometric_distSpec E p coin hcoin n`.
- Domain: every natural cap `n` and every `p ∈ [0,1]`, with an abstract
  Bernoulli(`p`) input callback. The actual guard/retry/counting term is matched.
- Law is the normalized capped-failure measure, with a Dirac-zero base and
  `p • dirac 0 + (1-p) • succ.map law_n` recurrence. It retains the cap atom.
- The single successor expectation lemma is a success/failure split using
  standard map integrals. Arbitrary ENNReal credits are retained.
- Pure integer cast bookkeeping is isolated outside the straight-line CTE proof.
- Independent build: `lake build SampLib.Samplers.BoundedGeometric` passed
  as part of `/tmp/samplib-review-discrete/bounded-uniform-build.log`.
- `lake env lean /tmp/samplib-review-discrete/BoundedAudit.lean` passed. It
  proves `law 0 n = dirac n`, `law 1 (n+1) = dirac 0`, and compiles a public-spec
  client preserving arbitrary Iris resource `I`.
- Core/public/expectation axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`. No corrective change was required.

### `uniformInt`: final acceptance

Reviewed file SHA256: `a54369681f648188ac924ba76c6bfc84a7458dedb66328d431b307f77f4a978c`.

- Public spec: `SampLib.UniformInt.uniformInt_distSpec E n [NeZero n]`.
- Every positive natural exclusive bound is supported; all mathematically valid
  integer bounds are such casts. Target is `uniformOfFinset (range n)`, encoded
  by `fun k : ℕ => Val.int (k : ℤ)`. Core additionally exposes `k < n`.
- Normalization now reuses installed
  `Measure.isProbabilityMeasure_uniformOfFinset`, resolving the review suggestion.
  Guard and sampled-index conversion facts are named pure lemmas outside logic.
- Own final build: `lake build SampLib.Samplers.FairCoin SampLib.Samplers.UniformInt`.
- Client check: `lake env lean /tmp/samplib-review-discrete/UniformFairAudit.lean`.
  Includes `law 1 = dirac 0` and an arbitrary-resource-preserving caller.
- Core, typed spec, and expectation audit use only standard Lean axioms.
- The two closedness simp lemmas strictly remove wrappers around the named
  sampler; no reverse rewrite or simp loop is introduced.

### `fairCoin`

Reviewed file SHA256: `24698d03ab4359a0afc0d974d2d1b6a332dea02a71f8e947ef36c9f9e3436f80`.

- Public spec: `SampLib.FairCoin.fairCoin_distSpec E`; core: `twp_fairCoin E F`.
- Generic lawful `rT` with actual uniform-integer primitive; target is the
  normalized fair Bernoulli law, using the existing half bias.
- The mathematical identity equates the mean over integer bits 0/1 with the fair
  expectation. There are no credit bounds or infinity exclusions.
- Review requests resolved: integer/toNat equality proof was moved out of the
  execution proof, and a named core theorem plus tiny public wrapper replaced
  the direct proof in the structure field.
- Same final own build/client command as `uniformInt`; the client retains an
  arbitrary Iris resource and composes this actual primitive with `IterateCoin`
  without unfolding either sampler proof.
- Core, public spec, and expectation audits have only standard Lean axioms.
- Shared open/close rewrites are directional wrapper elimination.

### `binomial`

Reviewed file SHA256: `76e53294152ed9586f37315a5f27e7257faca3e9bec707ff404c6653d6a9e996`.

- Public spec: `SampLib.Binomial.binomial_distSpec E p coin hcoin n`.
- Domain: every natural trial count and every unit-interval bias, with an abstract
  Bernoulli input callback. Actual code samples the coin, then the recursive
  count, then adds its indicator; the proof preserves that order.
- Target is the normalized n-fold independent Bernoulli-count convolution,
  specified mathematically by a Dirac-zero base and weighted identity/successor
  pushforwards. No execution measure occurs in its definition.
- One successor expectation lemma isolates the standard indicator-sum argument.
  Program logic is explicit finite induction and callback composition.
- Own build: `lake build SampLib.Samplers.Geometric SampLib.Samplers.Binomial`.
- `lake env lean /tmp/samplib-review-discrete/BinomialAudit.lean` passed, including
  `law 0 n = dirac 0`, `law 1 n = dirac n`, and arbitrary Iris resource framing.
- Core/public/math audits have only standard Lean axioms. No correction needed.

### `randomWalk`

Reviewed file SHA256: `b05909d65e4d4416a02ce57de895cd34742fd161b9c89671efd8dcf32f33d2a1`.

- Public spec: `SampLib.RandomWalk.randomWalk_distSpec E n`.
- Every natural length, including zero. Target is the normalized convolution of
  independent symmetric ±1 steps on integers; the program uses the actual
  verified integer `fairCoin` primitive, rather than an unsupported assumption.
- The continuation is integrated over the existing n-step law before the final
  step, matching program evaluation order. The expectation lemma uses standard
  map/add/constant-multiple integration and supports arbitrary credits.
- Own build: `lake build SampLib.Samplers.RandomWalk`.
- `lake env lean /tmp/samplib-review-discrete/RandomWalkAudit.lean` passed:
  zero-step law, one-step probability at +1 equal to 1/2, and a framed caller.
- Core/public/math audits have only standard Lean axioms.
- Seven explicit pure steps expose the recursive call without accidentally
  entering it. They are fixed symbolic execution, not search or a magic-repeat
  tactic; no correction was required.

### `geometric`

Reviewed file SHA256: `a5692d1af2f98bc791cb40d14c4ef0bb349873d411659fa6f2b70d552eb5ce78`.

- Public spec: `SampLib.Geometric.geometric_distSpec E p hp coin hcoin`.
- Full terminating domain `0 < p ≤ 1`, abstract input coin and generic lawful
  `rT`; no primitive-uniform assumption is needed. Counts failures before success.
- Target is mathlib's canonical `ProbabilityTheory.geometricMeasure`, not an
  operational recurrence. The mathematical recurrence is delegated to the
  independently reviewed distribution support lemma below.
- Amplification `k=1+p` remains strictly above one at p1. Success gets spare
  `pε` and failure gets `(1+p)ε`; exact credit preservation follows from
  `p²+(1-p)(1+p)=1`. The return branch discards only spare termination credit.
- Arbitrary ENNReal credits remain unrestricted; the canonical-law series and
  preservation arguments never coerce continuation credits to real values.
- Own module/source checks: `lake build SampLib.Samplers.Geometric` and
  `lake env lean SampLib/Samplers/Geometric.lean` passed (the latter checks the
  final source after the support recurrence was factored out).
- `lake env lean /tmp/samplib-review-discrete/GeometricAudit.lean` passed:
  p1 has mass one at zero and zero at every positive integer; a generic caller
  preserves arbitrary Iris resource; actual FairCoin composes as the input.
- Core/public/preservation axiom audits have only standard Lean axioms.

### Geometric distribution support

Reviewed `SampLib/Distributions/Geometric.lean` SHA256:
`f35eaf7977331250eb2152791b93d048be5f60d05e2c82a584a4d2b781624bd5`.

- Modern-module import of mathlib's canonical geometric measure plus one useful
  theorem `ProbabilityTheory.lintegral_geometricMeasure_succ p hp F`.
- Domain is `p ≠ 0`; the lemma splits its canonical probability series into
  the n0 term and the failure-weighted shifted tail. Every Nat-indexed ENNReal
  credit is admitted; countable measurability and nonnegative sum rearrangement
  justify the operations, including p1.
- Own source review and dependency build passed; its explicit axiom audit in
  `/tmp/samplib-review-discrete/NegativeBinomialAudit.lean` contains only
  `propext`, `Classical.choice`, and `Quot.sound`. This support is not counted as
  a sampler.

### `negativeBinomial`

Reviewed file SHA256: `7822adee15aa10c7ab49c8053746da73c0441bfbc07220dc787297370c2cdc84`.

- Public spec: `SampLib.NegativeBinomial.negativeBinomial_distSpec E p coin hcoin r hp`,
  where `hp : r = 0 ∨ 0 < (p : ℝ)`. This includes r0 at p0 and p1 at every r.
- Target is an independently defined finite convolution of canonical geometric
  failure laws, with Dirac-zero base. Product/map normalization is explicit.
- The expectation lemma is precisely the product-integral formula for the sum.
  Product order is recursive remainder first, geometric count second, matching
  ProbLang's right-to-left evaluation and the returned sum `x+y`.
- Program uses finite induction and the actual reviewed geometric spec, with
  arbitrary continuation credits. Eight explicit pure steps are fixed symbolic
  execution, not search. Closure rewrites are local and directional.
- Own build: `lake build SampLib.Samplers.NegativeBinomial`.
- `lake env lean /tmp/samplib-review-discrete/NegativeBinomialAudit.lean` passed:
  r0 law is Dirac zero, p1 law is Dirac zero for all r, a generic full-domain
  caller preserves arbitrary Iris resources, actual FairCoin composes as input,
  and r0+p0 theorem instantiation is accepted.
- Core/public/expectation and canonical-distribution-support audits use only
  standard Lean axioms. No correction was required.

### Inclusive and exclusive integer ranges

Reviewed file SHA256s:

- `SampLib/Samplers/RndInt.lean`: `c109e78be39b055f9e2af6082253a79d32d9d63c3f06be59615f776b8fee0178`.
- `SampLib/Samplers/RndIntRange.lean`: `ed36a99e9849300bee6a3fa35d10270ea6fe68f6d25fe1dc457465a24fa05c39`.
- `SampLib/Samplers/RndIntExcRange.lean`: `3307969caa795835b6ccc1c68db37333a6902b52859104bf27871ac96c234e51`.

Public specs and domains:

- `SampLib.RndInt.rndInt_distSpec E hi`: every natural inclusive upper bound,
  including zero. Target is uniform on `0,…,hi`.
- `SampLib.RndIntRange.rndIntRange_distSpec E lo hi h`: all signed integer
  `lo ≤ hi`, target inclusive uniform interval, including arbitrary singletons.
- `SampLib.RndIntExcRange.rndIntExcRange_distSpec E lo hi h`: all signed integer
  `lo < hi`, target half-open uniform interval. Width positivity and its NeZero
  instance are established from h, not exposed as an extra caller restriction.

The interval laws are ordinary translations of finite-uniform laws; the single
expectation lemma in each module is standard map integration (or finite averaging
for rndInt). Code guards, Nat/Int widths, singleton handling, and pure-evaluation
order match the actual terms. Arithmetic search remains outside execution proofs.
The public specs use actual previously reviewed UniformInt/RndInt proofs and need
only the uniform-integer primitive. Shared closure rewrites strictly remove
wrappers from concrete named terms. No change was required.

Own build: `lake build SampLib.Samplers.RndInt SampLib.Samplers.RndIntRange
SampLib.Samplers.RndIntExcRange` passed.
`lake env lean /tmp/samplib-review-discrete/RangesAudit.lean` passed, proving
zero-bound and arbitrary signed inclusive singleton laws, a negative width-one
exclusive law, and arbitrary-resource-preserving clients for all three public
specs. All nine core/public/expectation axiom audits contain only standard Lean
axioms.

### `rationalCoin`

Reviewed file SHA256: `d6ab18675de6d3f1fcd7cbd0036bfa174b0032f9d251c6ea4bfe780b02722eed`.

- Public spec: `SampLib.RationalCoin.rationalCoin_distSpec E a b ha hb hab`,
  with all integer inputs `0 ≤ a ≤ b`, `0 < b`. The target is the normalized
  Bernoulli law with probability `(a : ℝ)/(b : ℝ)`.
- The expectation lemma partitions the finite rank set into a successes and b-a
  failures, then divides both coefficients by b. Its local cast facts expose the
  two finite coefficients; continuation credits never undergo real conversion.
- Source guards and deterministic a0/a=b branches are exact. The nontrivial
  branch invokes the actual uniform-integer primitive and compares the sampled
  rank strictly below a. No hidden credit bounds or parameter restrictions occur.
- Review suggestion resolved: selected ENNReal openings shorten repeated
  qualification. The explicit ht/hf conversion facts were retained because they
  display the a and b-a coefficients directly, without new global scaffolding.
- Own build: `lake build SampLib.Samplers.RationalCoin`.
- `lake env lean /tmp/samplib-review-discrete/RationalAudit.lean` passed:
  both bias endpoints for arbitrary positive integer denominators, an arbitrary
  Iris-resource-preserving client, and actual RationalCoin(1/4)→VonNeumann
  composition via the public specs and closedness rewrites.
- Core/public/counting-expectation axiom audits contain only standard Lean axioms.

## Reproducible final review checks

All independent caller, boundary, and transitive-axiom checks above are now
consolidated in [DiscreteCallers.lean](DiscreteCallers.lean). The final command
`lake env lean agent-docs/reviews/DiscreteCallers.lean` passed against the final
accepted source hashes and current shared dependencies. It imports the proof
modules directly, adds no sampler assumptions beyond their public interfaces,
and preserves arbitrary caller resources. The separate JSON receipt contains
reviewer-owned direct hashes, full local import/implementation snapshots, and
configuration/policy/dependency context from `proof_dependencies.py`.
