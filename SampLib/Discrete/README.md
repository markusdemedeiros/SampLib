# Discrete

This directory holds the proofs for count laws, compound distributions, urns, and discrete tails.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (45)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.DiscreteExtra.betaBinomial` | $\mathrm{BetaBin}(n,\alpha,\beta)$ | [BetaBinomial](BetaBinomial.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L51) |
| `Occil.DiscreteExtra.betaNegativeBinomial` | $\mathrm{BetaNegBin}(r,\alpha,\beta)$ | [BetaNegativeBinomial](BetaNegativeBinomial.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L48) |
| `Occil.DiscreteExtra.binomialBinary` | $\mathrm{Bin}(n,a/b)$ | [BinomialBinary](BinomialBinary.lean) | [Binomial.lean](../../code/Samplers/Discrete/Binomial.lean#L49) |
| `Occil.DiscreteExtra.binomialHalfBits` | $\mathrm{Bin}(n,1/2)$ | [BinomialHalfBits](BinomialHalfBits.lean) | [Binomial.lean](../../code/Samplers/Discrete/Binomial.lean#L19) |
| `Occil.DiscreteExtra.binomialHalfRejection` | $\mathrm{Bin}(n,1/2)$ | [BinomialHalfRejection](BinomialHalfRejection.lean) | [Binomial.lean](../../code/Samplers/Discrete/Binomial.lean#L29) |
| `Occil.DiscreteExtra.borel` | $\mathrm{Borel}(\lambda)$ | [Borel](Borel.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L68) |
| `Occil.DiscreteExtra.compoundPoisson` | $\sum_{i=1}^{N}X_i,\ N\sim\mathrm{Pois}(\lambda)$ | [CompoundPoisson](CompoundPoisson.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L19) |
| `Occil.DiscreteExtra.cub` | $\pi(1+\mathrm{Bin}(m-1,1-p))+(1-\pi)\mathrm{Unif}\{1,\ldots,m\}$ | [Cub](Cub.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L75) |
| `Occil.DiscreteExtra.discreteLaplace` | $\Pr(K=k)\propto e^{-\epsilon\lvert k\rvert}$ | [DiscreteLaplace](DiscreteLaplace.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L38) |
| `Occil.DiscreteExtra.fisherHypergeometric` | $\Pr(K=k)\propto\binom ak\binom b{n-k}\omega^k$ | [FisherHypergeometric](FisherHypergeometric.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L30) |
| `Occil.DiscreteExtra.fisherMultivariate` | $\Pr(K=k)\propto\prod_i\binom{c_i}{k_i}w_i^{k_i},\ \sum_i k_i=n$ | [FisherMultivariate](FisherMultivariate.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L103) |
| `Occil.DiscreteExtra.generalizedGeometric` | $\Pr(K=k)=(1-\rho_k)\prod_{j<k}\rho_j$ | [GeneralizedGeometric](GeneralizedGeometric.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L96) |
| `Occil.DiscreteExtra.generalizedSibuya` | $\Pr(K=k)=\frac{\alpha}{\nu+k}\prod_{j<k}\left(1-\frac\alpha{\nu+j}\right)$ | [GeneralizedSibuya](GeneralizedSibuya.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L102) |
| `Occil.DiscreteExtra.himanshu` | $\mathrm{Geom}_0(p^m)$ | [Himanshu](Himanshu.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L115) |
| `Occil.DiscreteExtra.inversePolya` | $\mathrm{InversePolya}(r,a,b,c)$ | [InversePolya](InversePolya.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L39) |
| `Occil.DiscreteExtra.logUniform` | $\text{uniform logarithmic bucket, then uniform integer}$ | [LogUniform](LogUniform.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L53) |
| `Occil.DiscreteExtra.logarithmicSeries` | $\Pr(N=k)=-\frac{p^k}{k\log(1-p)}$ | [LogarithmicSeries](LogarithmicSeries.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L78) |
| `Occil.DiscreteExtra.multivariateHypergeometric` | $\Pr(K=k)=\frac{\prod_i\binom{c_i}{k_i}}{\binom{\sum_i c_i}n}$ | [MultivariateHypergeometric](MultivariateHypergeometric.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L95) |
| `Occil.DiscreteExtra.multivariatePoisson` | $(Z_0+Z_i)_i,\ Z_i\text{ independent Poisson}$ | [MultivariatePoisson](MultivariatePoisson.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L49) |
| `Occil.DiscreteExtra.negativeHypergeometric` | $\mathrm{NegHypergeom}(a,b,r)$ | [NegativeHypergeometric](NegativeHypergeometric.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L42) |
| `Occil.DiscreteExtra.negativeMultinomial` | $\mathrm{NegMultinomial}(r,w)$ | [NegativeMultinomial](NegativeMultinomial.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L60) |
| `Occil.DiscreteExtra.neymanTypeA` | $\mathrm{NeymanA}(\lambda,\mu)$ | [NeymanTypeA](NeymanTypeA.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L43) |
| `Occil.DiscreteExtra.polyaAeppli` | $\mathrm{PolyaAeppli}(\lambda,p)$ | [PolyaAeppli](PolyaAeppli.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L35) |
| `Occil.DiscreteExtra.polyaRational` | $\mathrm{NegBin}(r,p)$ | [PolyaRational](PolyaRational.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L21) |
| `Occil.DiscreteExtra.skellam` | $\mathrm{Pois}(\lambda_1)-\mathrm{Pois}(\lambda_2)$ | [Skellam](Skellam.lean) | [Compound.lean](../../code/Samplers/Discrete/Compound.lean#L27) |
| `Occil.DiscreteExtra.symmetricGeometric` | $\Pr(K=k)\propto(1-p)^{\lvert k\rvert}$ | [SymmetricGeometric](SymmetricGeometric.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L32) |
| `Occil.DiscreteExtra.walleniusHypergeometric` | $\mathrm{WalleniusHypergeom}(a,b,n,\omega)$ | [WalleniusHypergeometric](WalleniusHypergeometric.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L19) |
| `Occil.DiscreteExtra.walleniusMultivariate` | $\mathrm{WalleniusMultivariate}(n,c,w)$ | [WalleniusMultivariate](WalleniusMultivariate.lean) | [Urns.lean](../../code/Samplers/Discrete/Urns.lean#L82) |
| `Occil.DiscreteExtra.waringYule` | $\mathrm{BetaNegBin}(1,\alpha,\beta)$ | [WaringYule](WaringYule.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L57) |
| `Occil.DiscreteExtra.yuleSimon` | $\mathrm{YuleSimon}(\rho)$ | [YuleSimon](YuleSimon.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L62) |
| `Occil.DiscreteExtra.zeroTruncatedPoisson` | $\mathrm{Pois}(\lambda)\mid N>0$ | [ZeroTruncatedPoisson](ZeroTruncatedPoisson.lean) | [Counts.lean](../../code/Samplers/Discrete/Counts.lean#L88) |
| `Occil.DiscreteExtra.zeta` | $\Pr(K=k)=k^{-s}/\zeta(s)$ | [Zeta](Zeta.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L80) |
| `Occil.DiscreteExtra.zipf` | $\Pr(K=k)\propto k^{-s},\ 1\le k\le n$ | [Zipf](Zipf.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L68) |
| `Occil.binomial` | $\mathrm{Bin}(n,p)$ | [Binomial](Binomial.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L12) |
| `Occil.boundedGeometric` | $\min(\mathrm{Geom}_0(p),n)$ | [BoundedGeometric](BoundedGeometric.lean) | [Bounded.lean](../../code/Samplers/Discrete/Bounded.lean#L12) |
| `Occil.dice` | $\sum_{i=1}^n\mathrm{Unif}_i\{1,\ldots,s\}$ | [Dice](Dice.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L28) |
| `Occil.geometric` | $\mathrm{Geom}_0(p)$ | [Geometric](Geometric.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L20) |
| `Occil.hypergeometric` | $\mathrm{Hypergeom}(a+b,a,n)$ | [Hypergeometric](Hypergeometric.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L79) |
| `Occil.multinomial` | $\mathrm{Multinomial}(n,w/\sum_iw_i)$ | [Multinomial](Multinomial.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L54) |
| `Occil.negativeBinomial` | $\sum_{i=1}^r\mathrm{Geom}_{0,i}(p)$ | [NegativeBinomial](NegativeBinomial.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L23) |
| `Occil.poissonOne` | $\mathrm{Pois}(1)$ | [PoissonOne](PoissonOne.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L95) |
| `Occil.poissonRational` | $\mathrm{Pois}(x/y)$ | [PoissonRational](PoissonRational.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L106) |
| `Occil.polyaEggenberger` | $\mathrm{PolyaUrn}(n,a,b,c)$ | [PolyaEggenberger](PolyaEggenberger.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L70) |
| `Occil.randomWalk` | $\sum_{i=1}^n\mathrm{Unif}_i\{-1,1\}$ | [RandomWalk](RandomWalk.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L88) |
| `Occil.weightedChoice` | $\mathrm{Cat}(w)$ | [WeightedChoice](WeightedChoice.lean) | [Discrete.lean](../../code/Samplers/Discrete.lean#L33) |

## Contents

- Top level: 46 modules
- [`Laws/`](Laws): 43 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 1 modules with unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 14 modules with CTE loop invariants and other program-level helpers

---

`python3 agent-scripts/law_index.py` generates this file.
