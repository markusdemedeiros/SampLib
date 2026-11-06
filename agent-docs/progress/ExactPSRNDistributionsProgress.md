# Exact PSRN distributions progress

> These notes record round 2 and stopped changing on 6 November 2026. For the current
> status, see [LAWS.md](../../LAWS.md) and the [deferred samplers](../ExactCampaignDeferrals.md).

Family: "Lazy exact reals / Distributions" in
[Distributions.lean](../../code/Samplers/PSRN/Distributions.lean). All specs below are
`latent_real` (`LatentReal.IsLatentDistSpec`): the returned oracle keeps its whole
joint latent world, every finite precision and repeated aliases, with arbitrary
measurable ENNReal credit (including `∞`). Only `UniformInt` randomness is needed.

Author caller: [ExactPSRNDistributionsCallers.lean](../reviews/ExactPSRNDistributionsCallers.lean)
(construct, read the same handle twice, arbitrary frame and credit, boundary parameters,
`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`).

## Ready for review

| Sampler | Public spec | Domain | Class |
| --- | --- | --- | --- |
| `newGarima` | `SampLib.PSRNGammaFamilies.newGarima_latentDistSpec` | `n>0`, `d>0` (rate `θ=n/d`) | derived |
| `newIGarima` | `SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec` | `n>0`, `d>0` | derived |
| `newXgamma` | `SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec` | `n>0`, `d>0` | derived |
| `newWeightedExponentialGamma` | `SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec` | `n>0`, `d>0` | derived |
| `newMirra` | `SampLib.PSRNGammaFamilies.newMirra_latentDistSpec` | `n,d,an,ad>0` (`α=an/ad`) | derived |
| `newSushila` | `SampLib.PSRNLindleyFamilies.newSushila_latentDistSpec` | `n,d,a,b>0` (scale `a/b`) | derived |
| `newXLindley` | `SampLib.PSRNLindleyFamilies.newXLindley_latentDistSpec` | `n>0`, `d>0` | derived |

These domains are complete: outside them the source fails (its own guard, or the guards
of `rationalCoin`/`newExponential` on every branch).

Canonical laws: `*_model_law_density` gives the standard Garima, i-Garima, xgamma,
weighted exponential-gamma and Mirra densities;
`PSRNLindleyFamilies.xlindley_model_law` gives XLindley's density
`θ²(2+θ+x)e^{-θx}/(1+θ)²` (exponential = Γ(1,θ), so the outer selector folds into one
shape-one/two mixture); `sushila_model_law` is the Lindley density pushed forward by
`x ↦ x·a/b`.

Modules: `SampLib.Samplers.PSRNGammaFamilies`, `SampLib.Samplers.PSRNLindleyFamilies`,
with `SampLib.Syntax.PSRNGammaFamilies`, `SampLib.Syntax.PSRNLindleyFamilies`,
`SampLib.Distributions.PSRNGammaFamilySelectors`,
`SampLib.Distributions.PSRNGammaFamilyDensities`,
`SampLib.Distributions.PSRNDistributionMixtures`. They build only on accepted
`newGammaMixture`, `newLindley`, `newExponential`, `rationalCoin` specs and the
`LatentMixture`/`LatentRealConstructors` support; none is imported by `SampLib.lean` yet.

`newRayleigh` is already accepted ([ExactLatentBatch009](../reviews/ExactLatentBatch009.json));
its proof closure is frozen.

## Deferred

The other samplers share one missing piece: their rejection loops are written inline
(`rec retry u := ...`), not through `newRejection`. The accepted rejection kernels
([LatentRejectionKernel](../../SampLib/PSRN/Support/LatentRejectionKernel.lean),
[LatentLikelihoodRejection](../../attic/SampLib/LatentLikelihoodRejection.lean)) cover only
`newRejection`'s code. Each inline loop needs its own amplification proof, plus a
termination-domain proof for its `less` test on composite views.

- `newEpanechnikov`, `newArcCosine`: both call `newOrderStatistic`, which has no
  accepted spec (it is owned by `campaign_audit`). ArcCosine also needs a conditional
  `arctanFactory` coin and the alternating-trial parity law.
- `newHyperbolicSecant`: the envelope mathematics exists
  ([PSRNHyperbolicSecant](../../attic/SampLib/Distributions/PSRNHyperbolicSecant.lean)), as do
  `LatentSign`, `reciprocal_coinSpec` and `expMinusCoin_programSpec`. Still missing:
  the inline loop proof, and an `expMinusCoin` admissibility proof for the scaled view
  `2x` (floor-grid avoidance from the atomless exponential law). `expMinusCoin`'s spec
  is stated at `rT = ℝ`.
- `newContinuousBernoulli`: needs the inline loop over `newExponentialLogRate` with
  `less x 1` (the constant-view comparison is a.s. unequal), the truncated-exponential
  law and its identification with the continuous-Bernoulli density, and a spec for
  `subtract (rational 1) x`. Only right-subtraction of a rational has support today.
- `newCauchy`: inline loop over two uniforms with `less (x²+y²) 1` on shared operands,
  then `divide y x` (needs an a.s. `x ≠ 0` division domain).
- `newFGMCopula`, `newRectellipse` (`latent_vector`): inline vector rejection with a
  composite polynomial comparison. The FGM density mathematics exists
  ([PSRNFGM](../../attic/SampLib/Distributions/PSRNFGM.lean)). Rectellipse also adds two
  independent fair signs.
- `newTulap`: geometric difference, `integerPower` rational CDF bounds and two-sided
  truncation in the inline loop. No support exists.

No source defects were found; the algorithms match the stated target laws on paper.
