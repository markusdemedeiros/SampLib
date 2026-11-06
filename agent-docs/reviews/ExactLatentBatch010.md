# Independent exact sampler review: ExactLatentBatch010

Reviewer: `/root/review_exact_b`. All seven are `latent_real`, classification `derived`.

| Sampler | Public spec | Proof SHA-256 |
| --- | --- | --- |
| `Occil.PSRN.newGarima` | `SampLib.PSRNGammaFamilies.newGarima_latentDistSpec` | `be52aa3eea10aa06e088c7750e0c255ed82ebd07ee0270d542ba260f81b305a4` |
| `Occil.PSRN.newIGarima` | `SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec` | `be52aa3eea10aa06e088c7750e0c255ed82ebd07ee0270d542ba260f81b305a4` |
| `Occil.PSRN.newXgamma` | `SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec` | `be52aa3eea10aa06e088c7750e0c255ed82ebd07ee0270d542ba260f81b305a4` |
| `Occil.PSRN.newWeightedExponentialGamma` | `SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec` | `be52aa3eea10aa06e088c7750e0c255ed82ebd07ee0270d542ba260f81b305a4` |
| `Occil.PSRN.newMirra` | `SampLib.PSRNGammaFamilies.newMirra_latentDistSpec` | `be52aa3eea10aa06e088c7750e0c255ed82ebd07ee0270d542ba260f81b305a4` |
| `Occil.PSRN.newSushila` | `SampLib.PSRNLindleyFamilies.newSushila_latentDistSpec` | `8c475ef87fa79f545de20089afe2b374eb3b4fbbc7bc8fde7981a73fe160311e` |
| `Occil.PSRN.newXLindley` | `SampLib.PSRNLindleyFamilies.newXLindley_latentDistSpec` | `8c475ef87fa79f545de20089afe2b374eb3b4fbbc7bc8fde7981a73fe160311e` |

## Canonical laws

I compared each law with Occil's "Lindley Distribution and Lindley-Like Mixtures" table
(exporand.md) and the cited papers. With `θ = n/d`:

- Garima: weight `(θ+1)/(θ+2)`, shapes 1/2. Density `θ/(θ+2)(1+θ+θx)e^{-θx}` (Shanker 2016).
- i-Garima: weight `(θ+2)/(θ+3)`, shapes 1/2. Density `θ/(θ+3)(2+θ+θx)e^{-θx}`.
- Xgamma: weight `θ/(1+θ)`, shapes 1/3. Density `θ²/(1+θ)(1+θx²/2)e^{-θx}` (Sen et al. 2016).
- Weighted exponential-gamma (Iqbal and Iqbal 2020): weight `θ/(1+θ)`, shapes 2/3. Density
  `θ³x(2+x)/(2(1+θ))e^{-θx}`.
- Mirra (`α = an/ad`): the source weight `n²·ad/(an·d²+n²·ad)` equals `θ²/(α+θ²)`, shapes 1/3.
  Density `θ³/(α+θ²)(1+αx²/2)e^{-θx}`.
- XLindley: `θ/(1+θ)` selects Exp(θ), otherwise Lindley(θ). The prover folds the selector
  into one shape-1/2 mixture with weight `θ(θ+2)/(θ+1)²`. Density
  `θ²(2+θ+x)/(1+θ)²e^{-θx}` (Chouia and Zeghdoudi 2021).

The `*_model_law_density` and `xlindley_model_law` theorems state these densities, each
zero below 0. The selector identities transport the actual `rationalCoin` biases. Each
density is a theorem about the model in the public spec, not about some other mixture.

**Sushila.** Occil defines it as "α times a Lindley random variate" (note 2). The
`sushila_model_law` theorem states that definition: the canonical Lindley density pushed
forward by `x ↦ x·a/b`. That is adequate. To confirm it is the named family,
`ReviewExactLatent010.sushila_model_law_density` in the caller derives Shanker et al.
(2013)'s density `θ²/(α(θ+1))(1+x/α)e^{-θx/α}` from that pushforward. The proof uses a
change of variables (`Real.map_volume_mul_right`) and needs no extra axioms. A density
corollary in the module would match the other six, but it is optional.

## Domains

Each domain matches the source guards. On the complement every branch fails.

- Garima, i-Garima, xgamma and weighted exponential-gamma (`n>0, d>0`): the sources have
  no guard. Both mixture branches call `newGammaInteger` with shape 1, 2 or 3, which first
  calls `newExponential n d`. That call fails when `n<=0` or `d<=0`.
- Mirra (`n,d,an,ad>0`): the source's own guard covers `an` and `ad`, and the exponential
  guard covers `n` and `d`.
- Sushila (`n,d,a,b>0`): the source's own guard covers `a` and `b`, and `newLindley`'s
  guard covers `n` and `d`.
- XLindley (`n>0, d>0`): both branches, `newExponential` and `newLindley`, carry that guard.

Unreduced and negative-over-negative fractions are correctly excluded.

## Program logic and style

Literal openings (`Program.twp_*`) carry each wrapper to the accepted
`newGammaMixture_latentDistSpec`, Mixture or Lindley call, and reduce Mirra and Sushila
guards with one exact Boolean fact each. The gamma wrappers then apply the accepted mixture
spec unchanged. Sushila runs straight-line: `twp_bind` on the actual Lindley constructor,
then `twp_scaleRational` on the same state. XLindley instantiates `Mixture.latentDistSpec`
with the accepted rational-coin, exponential and Lindley specs. No spec assumes its own
sampler's law. Arbitrary measurable ENNReal credit, including infinity, passes through to
the whole joint latent world. All lines are at most 100 columns. The mathematics is
concise `field_simp; ring` algebra, with no simp forests.

Non-blocking nit: `PSRNDistributionMixtures.map_law` is unused.

## Checks

- Targeted gate build of both modules is clean.
- The `#audit_latent_real_spec` exact-head/noncircular audit prints `SPEC_OK` for all
  seven pairs.
- `#print axioms` for all seven public specs, all canonical-law theorems, the reviewer's
  Sushila density and the caller lists only `propext`, `Classical.choice` and `Quot.sound`.
- The caller (`ExactLatentBatch010Callers.lean`) compiles without warnings. For each
  sampler it constructs the actual source and reads the same returned closure twice, with
  an arbitrary framed Iris resource and arbitrary joint latent credit. Boundary cases
  include rate `1/1`, unreduced `6/4` and `4/2`, rate `1/9` and `9/1`, Mirra
  `α = 1/1000` and `1000`, Sushila scales `2/6` and `7/1`, precision 0 and reversed
  precisions, and infinite credit.
