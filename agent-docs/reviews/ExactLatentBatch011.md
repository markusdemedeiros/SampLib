# Independent exact sampler review: ExactLatentBatch011

Reviewer: `/root/review_exact_b`. All four are `latent_real`.

| Sampler | Public spec | Class | Proof SHA-256 |
| --- | --- | --- | --- |
| `Occil.PSRN.newOddsUniform` | `SampLib.PSRNOddsUniform.newOddsUniform_latentDistSpec` | derived | `170e7d0e0429ee3c822079658e6067d3da6fdcc0eb743985d11a5d79599413c9` |
| `Occil.PSRN.newRatioUniforms` | `SampLib.PSRNRatioUniforms.newRatioUniforms_latentDistSpec` | derived | `8fdda81a6d22b31c3a368c4fa0f3a2ad5f50561c7a711de0dfb79e346b38571e` |
| `Occil.PSRN.newPowerUniform` | `SampLib.PSRNPowerUniform.newPowerUniform_latentDistSpec` | core | `1f1451f2c06c145b89dcbd30780039a34bb2281cecdd03ebf15b7ee09e9bbe87` |
| `Occil.PSRN.newReciprocalPowerUniform` | `SampLib.PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec` | derived | `4d1b4fa412cd2763d26a46dc44281f460b4ffab95f0dfd045ad72f6633626750` |

`newSimplex` was reviewed in the same pass and is not accepted here (see the lead report).

## Laws

Occil's LAWS.md states these laws as transforms: `Lazy[U/(1-U)]`, `Lazy[U/V]`,
`Lazy[U^{a/b}]` and `Lazy[U^{-a/b}]`. Each `initial_law` theorem states exactly that
transform of the unit uniform (or of the independent product for `U/V`). This matches
the accepted precedent for `newUniformSum` (ExactLatentBatch003), whose law is the
recursive pushforward of the product uniform under addition. The odds law is also
identified canonically: `UniformOdds.law_eq_shifted_pareto` and `law_Iic` give the shifted
Pareto(1,1) law with CDF `t/(1+t)`. For `U/V`, the pushforward is Occil's law itself. A
closed-form CDF would be a bonus, not a gap. The caller adds two reviewer checks: the zero
exponent gives `dirac 1`, and the reciprocal power law equals the power law with numerator
`-a`.

## Domains

- Odds and ratio: the unit argument only; the sources have no guard.
- Power and reciprocal power: every integer `a` and every natural `b > 0`, passed as
  `#int b`. For `b <= 0`, `powerRational`'s guard fails. All branches are covered:
  `a = 0` (constant point oracle `1/1`, uniform allocated but unused), `a > 0` with `b = 1`
  (repeated squaring only, `root` returns its source), `a > 0` with `b >= 2` (bisection
  root), and `a < 0` (reciprocal of the positive branch, both root cases).

## Termination obligations (LatentObservationDomains.md)

These are proved, not assumed:

- `PSRNPowerUniform.ae_pos`: every dyadic posterior is a.s. positive. It follows from the
  unit law and posterior absolute continuity.
- `PSRNPowerUniform.admissible` proves `Root.Admissible (power a) b p` for every posterior
  `p`. Nonnegativity comes from `ae_pos`. For each rational threshold `(c/d)^b`, the
  equality `u^a = (c/d)^b` forces `u = ((c/d)^b)^{1/a}`. That point is null because the
  posterior is atomless (`ae_ne`). It is supplied in `twp_rooted` for the actual source
  cache.
- `rooted_nonzero` and `model_nonzero` give the reciprocal's nonzero denominator under
  every posterior. They are passed to `RepresentedReciprocal.twp_reciprocal`.
- Odds: `nonzero p` excludes the atom `u = 1` of `1 - u`. Ratio: `nonzero s` pushes
  `ae_ne 0` through the product's second projection. Both feed `RepresentedDivision`
  through `withInvariant`, so later reads keep them by absolute continuity.

## Program logic and style

Each constructor opens the actual `pl%` term with the literal `twp_pure`/`twp_bind` steps.
It applies the accepted `newUniform_representedDistSpec` with the arbitrary credit `F`, then
the existing arithmetic constructors (`twp_subtractFromPoint`, `RepresentedDivision`,
`IntegerPower.twp_integerPowerReal`, `Root.Program.twp_root`, `RepresentedReciprocal`). For
the ratio, the credit is split into left and right conditional expectations
(`ProductModel.expectation_left/right`), which is the joint world, not a scalar marginal.
`newReciprocalPowerUniform` uses the power's public latent spec as a black box. No spec
assumes its own sampler. The mathematics sits in short `mathematics` sections (`model_value`,
`initial_law`, `admissible`, `nonzero`).

Classifications follow precedent. Power is core: it is the first proof through the
integer-power and bisection-root support (as `newReciprocalUniform`/`newUniformSum` were core
for theirs). Odds and ratio are derived: they compose the accepted uniform with the division
and complement support. Reciprocal power is derived: it composes the power spec with the
reciprocal.

The shared support change in `LatentRepresentedComplement.lean` replaces `ieval (change …)`
with `simp only [Exp.ofVal]`. No statement changed, and the file builds cleanly.

Non-blocking nits: `UniformOdds.lean:45` is 102 columns. Otherwise the reviewed files are at
most 100 columns.

## Checks

- A targeted gate build of all five modules is clean (no warnings).
- The `#audit_latent_real_spec` exact-head and noncircular audit prints `SPEC_OK` for all
  four pairs.
- `#print axioms` for the four public specs, their `initial_law` theorems, the reviewer law
  checks and the caller lists only `propext`, `Classical.choice` and `Quot.sound`.
- The caller (`ExactLatentBatch011Callers.lean`) compiles without warnings. For each sampler
  it builds the actual source and reads the same returned closure twice. It keeps an
  arbitrary framed Iris resource and arbitrary or infinite measurable credit on the whole
  latent world (the product world for ratio). The power fixtures are `0/7`, `5/1`, `1/3`,
  `4/6`, `-1/1` and `-3/2`. The reciprocal-power fixtures are `0/1`, `2/5` and `-2/1`.
  The precisions include zero.
