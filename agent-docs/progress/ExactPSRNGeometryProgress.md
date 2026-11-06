# Exact PSRN geometry and uniform-transform progress

> These notes record round 2 and stopped changing on 6 November 2026. For the current
> status, see [LAWS.md](../../LAWS.md) and the [deferred samplers](../ExactCampaignDeferrals.md).

Owner: `psrn_geometry`. Owner-side callers: [PSRNGeometryCallers](../reviews/PSRNGeometryCallers.lean)
(arbitrary framed resource, arbitrary and infinite credits, aliased reads, domain boundaries).
All public specs below print only `propext`, `Classical.choice`, `Quot.sound`. Odds, ratio, power and
reciprocal power were accepted in [ExactLatentBatch011](../reviews/ExactLatentBatch011.json). Simplex is
resubmitted with a canonical law.

## Ready for review

| Sampler | Public spec | spec_kind | Class |
|---|---|---|---|
| `newSimplex` | `SampLib.PSRNSimplex.newSimplex_vectorSpec` | `latent_vector` | core |
| `newOddsUniform` | `SampLib.PSRNOddsUniform.newOddsUniform_latentDistSpec` | `latent_real` | derived |
| `newRatioUniforms` | `SampLib.PSRNRatioUniforms.newRatioUniforms_latentDistSpec` | `latent_real` | derived |
| `newPowerUniform` | `SampLib.PSRNPowerUniform.newPowerUniform_latentDistSpec` | `latent_real` | core |
| `newReciprocalPowerUniform` | `SampLib.PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec` | `latent_real` | derived |

Modules are `SampLib.Samplers.<name>` with the same suffix. Each scalar spec also has an
`..._representedDistSpec` carrying the actual interval schedule, for downstream reuse.

- **Simplex.** Domain: every `n ≥ 1`; `n ≤ 0` fails by the source guard. One unit-rate
  exponential world for every `n`. For `n = 1`, the source returns the constant unit oracle and
  allocates nothing; the world stays unobserved, with constant-one views. For `n ≥ 2`, the actual
  `repeatSample` exponentials are normalized by their one shared sum. The law is identified
  canonically in `PSRNSimplexOutput`: `output_law_uniform` gives `m!` times Lebesgue measure on
  `{y > 0, ∑ y < 1}` (with `m = n - 1`), completed by `1 - ∑ y`, and `output_firstCoordinates`
  gives the density form. The mathematics is in `Distributions/UniformSimplexLaw`: by induction,
  exponentials split into a `Gamma(m+1)` sum and an independent uniform simplex point. A
  `Beta(m+1, 1)` scaling then fills the next simplex, via the `u^m` Jacobian and a translation.
  The module chain is `PSRNSimplexModel/Allocation/Positive/Source/Singleton/Output`,
  `Samplers/PSRNSimplexMany`, and `Samplers/PSRNSimplex`. Review 011 rejected an earlier version
  that only restated the construction (`PSRNDirichletLaw.simplex`).
- **Odds.** Domain: unit argument only. One uniform `u`, output `u / (1 - u)`. The numerator and
  the complement read the same cache. The law is `UniformOdds.law`, the shifted Pareto(1, 1).
  `1 - u ≠ 0` holds a.s. under every posterior.
- **Ratio.** Domain: unit argument only. Two independent uniforms share one product world. The
  output is `a / b`, and `b ≠ 0` holds a.s. The law is identified as the pushforward of the
  product uniform law under division. No closed-form CDF is proved.
- **Power.** Domain: every integer numerator `a` and every denominator `b > 0`; `b ≤ 0` fails.
  The law is `unitLaw.map (u ↦ u ^ (a / b))`. All source branches are covered:
  `a = 0` returns the constant unit oracle, `a > 0` runs repeated squaring and then a root (or
  returns the power when `b = 1`), and `a < 0` takes the reciprocal of that. The root's comparison
  domain (`Root.Admissible`) and the reciprocal's nonzero denominator follow from `u > 0` a.s.
- **Reciprocal power.** Domain and law match the power, with exponent `-a / b`. It composes the
  power spec with the actual reciprocal.

Shared support touched: `LatentRepresentedComplement.lean` (unimported, previously failed to
parse). Two `ieval (change … pl(…))` steps became `simp only [Exp.ofVal]`. No statement changed.

## Deferred

- **`newSphere`, `newBall`, `newShell`.** Blocked: `newSphere` (n ≥ 2) calls `repeatSample
  newGaussian`, and no `newGaussian` latent spec exists yet. Ball and shell call `newSphere`. Once
  Gaussian lands, Ball can reuse `PSRNPowerUniform` (`a = 1, b = n`). Shell also needs
  `root` of an affine uniform, with an admissibility proof.
- **`newDirichlet`.** Blocked: it calls `newGamma`, which has no latent spec yet (psrn_gamma).
  The normalization support (`LatentNormalization*`, `LatentDivideCoordinates`) used by simplex
  applies unchanged once a represented gamma constructor exists.
- **`newOrderStatistic`.** Not started. The read protocol exists (`LatentOrderStatisticModel/
  Oracle`). Missing: the constructor proof, which needs a recursive insertion-sort invariant over a
  growing uniform-vector world, with every `less` comparison on the joint posterior, plus `getAt`.
  This is a substantial new proof; no partial files were added.
