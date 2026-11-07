# General

This directory holds the proofs for general schemes: Markov chains, coupling from the past, Metropolis sampling, and point selection.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (42)

Each of these samplers has an accepted proof in this directory:

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.General.bootstrap` | $\left(\widehat\mu^{\otimes n}\right)^{\otimes B}$ | [Bootstrap](Bootstrap.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L16) |
| `Occil.General.classifiedModel` | $\sum_i\frac{w_i}{\sum_jw_j}(\delta_i\otimes\mu_i)$ | [ClassifiedModel](ClassifiedModel.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L117) |
| `Occil.General.couplingFromPast` | $\pi,\quad\pi K=\pi$ | [CouplingFromPast](CouplingFromPast.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L237) |
| `Occil.General.discreteCDF` | $\Pr(K=i)=(C_i-C_{i-1})/C_{n-1}$ | [DiscreteCDF](DiscreteCDF.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L56) |
| `Occil.General.episodes` | $(\sum_{i=1}^{N}X_i,N)$ | [Episodes](Episodes.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L392) |
| `Occil.General.generativeModel` | $g_*\mu$ | [GenerativeModel](GenerativeModel.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L110) |
| `Occil.General.gibbsSweep` | $(K_1\cdots K_d)(x,\cdot)$ | [GibbsSweep](GibbsSweep.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L279) |
| `Occil.General.groupedPermutation` | $\mathrm{Unif}(\text{fixed-size position partitions})$ | [GroupedPermutation](GroupedPermutation.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L38) |
| `Occil.General.histogram` | $\Pr(X=x)=\frac{c_i}{(a_{i+1}-a_i)\sum_jc_j},\ a_i\le x<a_{i+1}$ | [Histogram](Histogram.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L53) |
| `Occil.General.incompleteInformation` | $\mathrm{Cat}(p)$ | [IncompleteInformation](IncompleteInformation.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L188) |
| `Occil.General.inverseCDF` | $\Pr(X\le x)=C(x)/s$ | [InverseCDF](InverseCDF.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L72) |
| `Occil.General.inverseQuantile` | $Q_*\mathrm{Unif}\{1,\ldots,s-1\}$ | [InverseQuantile](InverseQuantile.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L49) |
| `Occil.General.kernelDensity` | $\widehat\mu*\kappa$ | [KernelDensity](KernelDensity.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L74) |
| `Occil.General.kernelDensityVector` | $\widehat\mu*\kappa^{\otimes d}$ | [KernelDensityVector](KernelDensityVector.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L81) |
| `Occil.General.latinHypercube` | $\text{independent shuffled stratifications by coordinate}$ | [LatinHypercube](LatinHypercube.lean) | [Points.lean](../../code/Samplers/General/Points.lean#L160) |
| `Occil.General.latinHypercube1D` | $\text{uniform shuffle of stratified draws}$ | [LatinHypercube1D](LatinHypercube1D.lean) | [Points.lean](../../code/Samplers/General/Points.lean#L155) |
| `Occil.General.markovChain` | $K^n(x,\cdot)$ | [MarkovChain](MarkovChain.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L207) |
| `Occil.General.markovStep` | $K(x,\cdot)$ | [MarkovChain](MarkovChain.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L203) |
| `Occil.General.markovTrajectory` | $\prod_{t=1}^n K(x_{t-1},dx_t)$ | [MarkovTrajectory](MarkovTrajectory.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L213) |
| `Occil.General.metropolis` | $K_{\mathrm{Metropolis}}^n(x,\cdot)$ | [CountableMetropolis](CountableMetropolis.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L273) |
| `Occil.General.metropolisHastings` | $K_{\mathrm{MH}}^n(x,\cdot)$ | [CountableMetropolisHastings](CountableMetropolisHastings.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L258) |
| `Occil.General.pdfRejection` | $\Pr(X=x)\propto h(x),\ x\in\{\ell,\ldots,u-1\}$ | [PdfRejection](PdfRejection.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L85) |
| `Occil.General.perfectFiniteChain` | $\pi,\quad\pi K=\pi$ | [PerfectFiniteChain](PerfectFiniteChain.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L250) |
| `Occil.General.permutationSamples` | $\mathrm{Unif}(S_n)^{\otimes B}$ | [PermutationSamples](PermutationSamples.lean) | [DataModels.lean](../../code/Samplers/General/DataModels.lean#L23) |
| `Occil.General.permutationTest` | $\frac{1+\lvert\{i:T(\Pi_i x)\ge T(x)\}\rvert}{B+1}$ | [PermutationTest](PermutationTest.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L344) |
| `Occil.General.piecewiseConstant` | $\Pr(X=x)\propto h_i,\ a_i\le x<a_{i+1}$ | [PiecewiseConstant](PiecewiseConstant.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L102) |
| `Occil.General.piecewiseLinear` | $\Pr(X=x)\propto h_i+\frac{x-a_i}{a_{i+1}-a_i}(h_{i+1}-h_i)$ | [PiecewiseLinear](PiecewiseLinear.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L123) |
| `Occil.General.randomDateTime` | $\mathrm{Unif}\{\ell,\ldots,h\}$ | [RandomDateTime](RandomDateTime.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L42) |
| `Occil.General.randomMap` | $\bigotimes_i K(i,\cdot)$ | [RandomMap](RandomMap.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L221) |
| `Occil.General.randomScanGibbs` | $\left(d^{-1}\sum_i K_i\right)^n(x,\cdot)$ | [RandomScanGibbs](RandomScanGibbs.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L287) |
| `Occil.General.randomString` | $\mathrm{Unif}(\text{alphabet})^{\otimes n}$ | [RandomString](RandomString.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L38) |
| `Occil.General.randomWalkPath` | $(x,x+X_1,\ldots,x+\sum_{i=1}^n X_i)$ | [RandomWalkPath](RandomWalkPath.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L357) |
| `Occil.General.refinedCDFComparison` | $\mathrm{Bern}(\mathbf{1}_{\{U<F(x)\}})\mid U$ | [RefinedCDFComparison](RefinedCDFComparison.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L173) |
| `Occil.General.refinedCoin` | $\mathrm{Bern}(p)$ | [RefinedCoin](RefinedCoin.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L157) |
| `Occil.General.shapeRejection` | $\mu(\cdot\mid A)$ | [ShapeRejection](ShapeRejection.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L97) |
| `Occil.General.sliceSampler` | $K_{\mathrm{slice}}^n(x,\cdot)$ | [SliceSampler](SliceSampler.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L303) |
| `Occil.General.stoppedMaximum` | $\max_{1\le i\le N}X_i$ | [StoppedMaximum](StoppedMaximum.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L382) |
| `Occil.General.stoppedMinimum` | $\min_{1\le i\le N}X_i$ | [StoppedMinimum](StoppedMinimum.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L373) |
| `Occil.General.stoppedSum` | $\sum_{i=1}^{N}X_i$ | [StoppedSum](StoppedSum.lean) | [Core.lean](../../code/Samplers/General/Core.lean#L366) |
| `Occil.General.stratified1D` | $\bigotimes_i\mathrm{Unif}\{\lfloor is/n\rfloor,\ldots,\lfloor(i+1)s/n\rfloor-1\}$ | [Stratified1D](Stratified1D.lean) | [Points.lean](../../code/Samplers/General/Points.lean#L145) |
| `Occil.General.stratifiedBox` | $\text{independent uniform draws per grid cell}$ | [StratifiedBox](StratifiedBox.lean) | [Points.lean](../../code/Samplers/General/Points.lean#L182) |
| `Occil.General.uniformBoxPoint` | $\mathrm{Unif}\{0,\ldots,s-1\}^{\otimes d}$ | [UniformBoxPoint](UniformBoxPoint.lean) | [Points.lean](../../code/Samplers/General/Points.lean#L226) |

## Contents

The directory holds these modules:

- Top level: 49 modules
- [`Laws/`](Laws): 44 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 6 modules with unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 8 modules with CTE loop invariants and other program-level helpers

---

`python3 agent-scripts/law_index.py` generates this file.
