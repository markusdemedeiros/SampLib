# Exact deferred vector sampler review, batch 002

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.PSRNSimplex.newSimplex_vectorSpec`, SHA-256
`c97cca07e257b18c254be3558d04849928aa855aa8491bc00c304d8908769be8`.

The domain is every dimension `n >= 1`. For `n <= 0`, the actual source guard fails. The
result is the actual list of `n` jointly owned deferred coordinate oracles over one
unit-rate exponential world. It keeps arbitrary measurable joint ENNReal credit, including
infinity, and supports all natural read precisions and repeated aliases. For `n = 1`, the
source returns the constant oracle `1/1` and allocates nothing, so the world stays
unobserved. For `n >= 2`, the actual `repeatSample` exponentials are divided by their one
shared sum.

## Canonical law

The first submission was not accepted. Its law, `PSRNDirichletLaw.simplex`, is defined as
normalized iid Exp(1), which is the algorithm's own construction. Occil names the law
`Unif(Δ_d)`. The resubmission adds the canonical identification:

- `UniformSimplex.law m` is `m!` times Lebesgue measure on
  `{y in R^m | y > 0, sum y < 1}`, and `embed` appends `1 - sum y`.
- `UniformSimplex.simplex_eq` proves that `simplex (m+1)` equals `(law m).map embed`. It
  integrates against arbitrary measurable `F`. `lintegral_exponentials` proves by induction
  that the iid exponentials factor into a `Gamma(m+1)` sum `s` and an independent uniform
  simplex point, with `x = s • embed y`. The step uses the existing beta–gamma split
  (`BetaExponentialProduct.gamma_pair_transform`). `lintegral_beta_fill` shows that a
  `Beta(m+1,1)` scaling of an `m`-simplex point fills the `(m+1)`-simplex. It uses the
  Jacobian `u^m` (`Measure.map_addHaar_smul`) and a translation of the last coordinate.
  Normalization then cancels `s` almost everywhere.
- `PSRNSimplex.output_law_uniform` and `output_firstCoordinates` state this law for
  `vectorLaw (world (m+1)) (output (m+1)) (initial (m+1))`. These are the same `world`,
  `output` and `initial` that `newSimplex_vectorSpec` uses, so the theorem is about the
  spec's own model.

The caller adds two reviewer checks. For `n = 3`, the first two coordinates have density 2
on the open triangle. For `n = 1`, the law is the point mass at `(1)`, obtained from
`output_law_uniform 0`.

## Protocol and program

`many_payloadSpec` opens the actual source and steps through both guards. It applies the
accepted-style `PiModel.repeatSample_vectorSpec` allocation over the actual
`newExponential 1 1` callback, then `Normalization.twp_constructor`. The common sum's
nonzero invariant is proved jointly (`initial_nonzero`, from a.s. positive gamma
coordinates). Absolute continuity carries it to every refinement. Coordinate views come
from `Normalization.coordinateSpec`. Each view observes the shared family, so no marginal
is substituted. The singleton branch is straight-line `twp_pures` plus the value.

## Presentation

`UniformSimplexLaw.lean` keeps the mathematics in two central lemmas, an induction and a
fill lemma, each a commented `calc`. Its helpers are standard: region measurability, the
snoc split and the scaling Jacobian. The measurability terms are long but direct. There
are no simp forests or debugging residue.

Non-blocking nit: line 7 of the docstring in `SampLib/Samplers/PSRNSimplex.lean` is 143
columns. All other reviewed lines are at most 100.

## Checks

- A targeted gate build of `SampLib.Samplers.PSRNSimplex` is clean (no warnings).
- `#audit_latent_vector_spec` prints `SPEC_OK` for the exact head `Occil.PSRN.newSimplex`
  and finds no circular premise.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for the public
  spec, `output_law_uniform`, `output_firstCoordinates`, `simplex_eq`, the caller theorem
  and both reviewer law checks.
- The caller (`ExactLatentVectorBatch002Callers.lean`) compiles without warnings. It builds
  the actual source for every `n >= 1` under an arbitrary framed Iris resource, then reads
  coordinates `i` and `j` of the returned handles. `i = j` is the alias case. Arbitrary or
  infinite credit stays on the whole exponential world. The fixtures cover `n = 1` (alias
  at precision 0, infinite credit), `n = 2` (distinct coordinates), `n = 3`, and general
  `n`.
