# Exact structured samplers: initial domain and interface audit

Reviewer: `/root/review_exact_b`. Dependency context: `clutch-lean` `06a7b3e2`.
This source/design audit accepts no proofs. Acceptance requires the independent
caller, axiom and full source-snapshot checks in each later numbered receipt.

## Exact discrete distributions

The generalized-geometric continuation interface needs mathematical survival
probabilities tending to zero. A callback returning false with some positive
unconditional probability is insufficient after conditioning on previous outcomes.
Rational-power coins, Zipf and zeta inherit the fractional-power endpoint and
termination obligations. Beta-negative-binomial and urn families must retain
positive parameter denominators and the actual source's count/support convention.
A recurrence for output probabilities without termination is not a CTE proof.

## Integer and weighted sampling

`voseDraw` already has a full ownership-preserving categorical theorem in
`SampLib.AliasTable.voseDraw_ownedDistSpec`. Its separate acceptance is an interface
review, not new mathematics. All threshold and alias cells remain owned; zero
weights are allowed and positive total weight is required.

Systematic inclusion sampling uses one shared shift. Its intended joint law is
not independent Bernoulli inclusion. A pushforward law is a suitable representation,
but a useful theorem must also expose sample cardinality and prescribed inclusion
probabilities. Splitting similarly needs its full joint transition invariant.
Tree and optimal samplers require prefix-mass conservation and termination;
recycling requires the joint entropy-pool invariant across successive samples.

## General sampling

`markovStep_distSpec` already proves arbitrary-credit sampling from the normalized
selected row. A single step permits rectangular matrices: only the selected row's
positive mass and valid row index are necessary. The square-matrix invariant is
needed by iteration, not by this standalone theorem.

`shapeRejection` is a derived wrapper around generic rejection. Its premises must
specify only the proposal law and correct membership test; the positive acceptance
mass supplies termination. Conditioning may have mass one.

Refinement algorithms keep one lazy uniform. Correctness needs convergent bounds,
shared posterior ownership and a zero-mass unresolved equality event. Replacing
successive observations by fresh uniforms changes the program's law.

## Lazy exact reals

PSRN constructors return object-language interval-oracle closures, not real
literals. A scalar `IsDistSpec` on a fictitious real return does not specify them.
Constructor allocation, owned observation rules, posterior continuation credit
and a compositional deferred-law interface are necessary.

The same cached root may have multiple aliases. Arithmetic and observations must
thread one ownership state, preserving the joint latent law. In particular:

- Cauchy reuses both coordinates in the rejection radius and returned ratio.
- FGM and rectellipse reuse accepted coordinates after conditioning on acceptance.
- Sphere, ball, shell and Dirichlet share normalizers/radii among coordinates.
- Hyperbolic-secant rejection invokes a coin conditional on its cached exponential
  proposal; an unconditional mixture bias cannot replace this conditional law.
- Equal nondegenerate oracle values may defeat comparison. Separation/continuity
  and rational-threshold exceptional sets belong in termination arguments.
- Conditional digit streams may have atoms or dependent tails; the interface must
  not fill unsampled digits with independent fair bits without a stated law.

Fresh draws may be independent, but repeated observations of one lazy value are
not. The posterior credit must cover arbitrary measurable ENNReal functions,
including infinity, and caller resources must survive every observation.
