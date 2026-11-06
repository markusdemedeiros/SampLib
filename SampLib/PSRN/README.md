# PSRN

Lazy exact reals: arithmetic, observations and exact continuous samplers.

Part of the [library layout](../README.md#layout).

## Verified samplers (27)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.PSRN.coin` | $\mathrm{Bern}(x)\ \text{conditional on cached }x$ | [PSRNCoin](Support/PSRNCoin.lean) | [Core.lean](../../code/Samplers/PSRN/Core.lean#L100) |
| `Occil.PSRN.expMinusCoin` | $\mathrm{Bern}\!\left(e^{-x}\right)$ | [PSRNExpMinusCoin](PSRNExpMinusCoin.lean) | [Exponential.lean](../../code/Samplers/PSRN/Exponential.lean#L53) |
| `Occil.PSRN.newExponential` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | [PSRNExponentialRational](PSRNExponentialRational.lean) | [Exponential.lean](../../code/Samplers/PSRN/Exponential.lean#L32) |
| `Occil.PSRN.newExponentialFromDecay` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | [PSRNExponential](Support/PSRNExponential.lean) | [Exponential.lean](../../code/Samplers/PSRN/Exponential.lean#L19) |
| `Occil.PSRN.newExponentialLogRate` | $\mathsf{Lazy}[\mathrm{Exp}(\log(x/y))]$ | [PSRNExponentialLogRate](PSRNExponentialLogRate.lean) | [Exponential.lean](../../code/Samplers/PSRN/Exponential.lean#L39) |
| `Occil.PSRN.newExponentialUnknownRate` | $\mathsf{Lazy}[\mathrm{Exp}(p)]$ | [PSRNExponentialUnknownRate](PSRNExponentialUnknownRate.lean) | [Exponential.lean](../../code/Samplers/PSRN/Exponential.lean#L46) |
| `Occil.PSRN.newGammaInteger` | $\mathsf{Lazy}[\mathrm{Gamma}(k,\lambda)]$ | [PSRNGammaInteger](PSRNGammaInteger.lean) | [BetaGamma.lean](../../code/Samplers/PSRN/BetaGamma.lean#L60) |
| `Occil.PSRN.newGammaMixture` | $\mathsf{Lazy}[\text{Gamma mixture}]$ | [PSRNGammaMixture](PSRNGammaMixture.lean) | [BetaGamma.lean](../../code/Samplers/PSRN/BetaGamma.lean#L67) |
| `Occil.PSRN.newGarima` | $\mathsf{Lazy}[\mathrm{Garima}]$ | [PSRNGammaFamilies](PSRNGammaFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L125) |
| `Occil.PSRN.newIGarima` | $\mathsf{Lazy}[\text{I Garima}]$ | [PSRNGammaFamilies](PSRNGammaFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L128) |
| `Occil.PSRN.newInsideShape` | $\mathsf{Lazy}[\mathrm{Unif}(A)]$ | [PSRNInsideShape](PSRNInsideShape.lean) | [Core.lean](../../code/Samplers/PSRN/Core.lean#L105) |
| `Occil.PSRN.newLindley` | $\mathsf{Lazy}[\mathrm{Lindley}]$ | [PSRNLindley](PSRNLindley.lean) | [BetaGamma.lean](../../code/Samplers/PSRN/BetaGamma.lean#L73) |
| `Occil.PSRN.newMirra` | $\mathsf{Lazy}[\mathrm{Mirra}]$ | [PSRNGammaFamilies](PSRNGammaFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L137) |
| `Occil.PSRN.newOddsUniform` | $\mathsf{Lazy}[U/(1-U)]$ | [PSRNOddsUniform](PSRNOddsUniform.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L87) |
| `Occil.PSRN.newPowerUniform` | $\mathsf{Lazy}[U^{a/b}]$ | [PSRNPowerUniform](PSRNPowerUniform.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L32) |
| `Occil.PSRN.newRatioUniforms` | $\mathsf{Lazy}[U/V]$ | [PSRNRatioUniforms](PSRNRatioUniforms.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L77) |
| `Occil.PSRN.newRayleigh` | $\mathsf{Lazy}[\mathrm{Rayleigh}]$ | [PSRNRayleigh](PSRNRayleigh.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L18) |
| `Occil.PSRN.newReciprocalPowerUniform` | $\mathsf{Lazy}[U^{-a/b}]$ | [PSRNReciprocalPowerUniform](PSRNReciprocalPowerUniform.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L83) |
| `Occil.PSRN.newReciprocalUniform` | $\mathsf{Lazy}[1/U]$ | [PSRNReciprocalUniform](PSRNReciprocalUniform.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L80) |
| `Occil.PSRN.newRejection` | $\mathsf{Lazy}[\mu(\cdot\mid A)]$ | [PSRNRejection](PSRNRejection.lean) | [Core.lean](../../code/Samplers/PSRN/Core.lean#L93) |
| `Occil.PSRN.newSimplex` | $\mathsf{Lazy}[\mathrm{Unif}(\Delta_d)]$ | [PSRNSimplex](PSRNSimplex.lean) | [Geometry.lean](../../code/Samplers/PSRN/Geometry.lean#L91) |
| `Occil.PSRN.newSushila` | $\mathsf{Lazy}[\mathrm{Sushila}]$ | [PSRNLindleyFamilies](PSRNLindleyFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L142) |
| `Occil.PSRN.newUniformSum` | $\mathsf{Lazy}[\sum_{i=1}^nU_i]$ | [PSRNUniformSum](PSRNUniformSum.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L72) |
| `Occil.PSRN.newWeightedExponentialGamma` | $\mathsf{Lazy}[\text{Weighted Exponential Gamma}]$ | [PSRNGammaFamilies](PSRNGammaFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L131) |
| `Occil.PSRN.newXLindley` | $\mathsf{Lazy}[\text{X Lindley}]$ | [PSRNLindleyFamilies](PSRNLindleyFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L147) |
| `Occil.PSRN.newXgamma` | $\mathsf{Lazy}[\mathrm{Xgamma}]$ | [PSRNGammaFamilies](PSRNGammaFamilies.lean) | [Distributions.lean](../../code/Samplers/PSRN/Distributions.lean#L134) |
| `Occil.PSRN.powerCoin` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [PSRNPowerCoin](PSRNPowerCoin.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L39) |

## Contents

- 21 top-level modules
- [`Laws/`](Laws): 33 modules, target laws, kernels and expectation lemmas
- [`Syntax/`](Syntax): 19 modules, unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 94 modules, CTE loop invariants and program-level helpers

---

Generated by `python3 agent-scripts/law_index.py`.
