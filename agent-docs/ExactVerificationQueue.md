# Exact sampler verification queue

Snapshot: 2026-11-06, from `LAWS.md` and implementation inspection.
**137 existing sampler entries without accepted standalone proofs**, after excluding all 224
entries catalogued as numerical and another 11 grid/numerical implementations filed under
General sampling. This counts code entries, not 137 independent algorithms or guaranteed proofs.
Every listed entry already has implementation code. Source-wide missing implementations remain
a separate audit; `LAWS.md` is an implementation catalogue, not an exhaustive Occil checklist.

| Family | Entries |
| --- | ---: |
| Ordinary Bernoulli factories | 33 |
| Constant coins | 27 |
| Lazy coin factories | 3 |
| Lazy exact-real samplers | 46 |
| Exact discrete distributions | 11 |
| Integer and weighted sampling | 12 |
| General exact sampling | 5 |
| Total | 137 |

## Order of attack

1. Weighted/integer samplers: inclusion splitting/systematic selection; loaded dice, Knuth–Yao,
   Han–Hoshi; sorted/succinct/optimal selection; entropy recycling. Shared tree and entropy-pool
   mathematics matters more than the new elementary real operators.
2. Discrete distributions: generalized geometric/Sibuya, beta-negative-binomial, rational Pólya,
   inverse Pólya, Waring–Yule/Yule–Simon; then Zipf/zeta through rational-power coin support.
3. General exact interfaces: rejection into a shape, matrix transition, refinement-based coins
   and finite inverse CDF with incomplete information.
4. Bernoulli/constant families listed below; choose groups around one expectation-preservation
   argument, preserving each actual source algorithm. New native-real terms are a different queue.
5. Lazy exact reals: establish owned shared-latent semantics and joint arithmetic/observation
   rules, then uniform/exponential/Gaussian/gamma/beta and their transformations. These 46 are
   substantial proof work; scalar marginal laws alone do not justify correlated/shared uses.

## Qualifications

- `linearLowProbability`: advertised law is known false; repair or exclude, not a routine proof.
- `rationalContinuedFraction`: unrestricted positive inputs can diverge; restrict the domain.
- `sampleGeometricBag` and `voseDraw`: supporting coin/owned distribution theorems already exist;
  check the public interface/index rather than counting them as wholly unproved algorithms.
- Several rows are wrappers, transitions or callbacks. Count such support honestly, without
  inflating a proof total by presenting every helper as a fresh sampling technique.
- All proof work follows [VerifyingSamplers.md](VerifyingSamplers.md). Dependency-update build
  results do not renew historical independent-review receipts for a changed dependency context.

## Individual entries

### Bernoulli factories / Basic (1)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.fractionalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Basic.lean](../code/Samplers/Bernoulli/Basic.lean#L51) |

### Bernoulli factories / Elementary (3)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.complementOverLogInverse` | $\mathrm{Bern}\!\left(\frac{1-p}{\log(1/p)}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L107) |
| `Occil.FactoryExtra.expIntegral` | $\mathrm{Bern}\!\left(\frac{1-e^{-(m+p)}}{m+p}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L71) |
| `Occil.FactoryExtra.pOverLogInverseComplement` | $\mathrm{Bern}\!\left(\frac p{\log(1/(1-p))}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L101) |

### Bernoulli factories / Exponential (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.binaryExponential` | $\mathrm{Bern}\!\left(2^{-m(k+p)}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L88) |
| `Occil.FactoryExtra.binaryExponentialRational` | $\mathrm{Bern}\!\left(2^{-ap/b}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L98) |
| `Occil.FactoryExtra.expDivThree` | $\mathrm{Bern}\!\left(e^p/3\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L65) |
| `Occil.FactoryExtra.expMinusExp` | $\mathrm{Bern}\!\left(e^{-e^{m+p}}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L72) |
| `Occil.FactoryExtra.expSquareTimesComplement` | $\mathrm{Bern}\!\left(e^{p^2}(1-p)\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L82) |

### Bernoulli factories / Linear (3)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.linear2014` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L129) |
| `Occil.FactoryExtra.linearLowProbability` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L93) |
| `Occil.FactoryExtra.linearPowerWalk` | $\mathrm{Bern}\!\left((cp)^m\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L108) |

### Bernoulli factories / Polynomials (3)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.polynomial` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L19) |
| `Occil.FactoryExtra.rationalFunction` | $\mathrm{Bern}\!\left(f(p)/g(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L48) |
| `Occil.FactoryExtra.threePointPiecewise` | $\mathrm{Bern}(f(p)),\ f\text{ piecewise affine}$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L57) |

### Bernoulli factories / Powers (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.rationalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L15) |
| `Occil.FactoryExtra.twoCoinPower` | $\mathrm{Bern}\!\left(p^q\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L24) |

### Bernoulli factories / Series (6)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.alternatingSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}(-1)^nc_np^n\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L20) |
| `Occil.FactoryExtra.envelopeFactory` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L118) |
| `Occil.FactoryExtra.envelopeFactoryDegrees` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L79) |
| `Occil.FactoryExtra.minimumComplement` | $\mathrm{Bern}\!\left(\min(p,1-p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L135) |
| `Occil.FactoryExtra.minimumHalf` | $\mathrm{Bern}(\min(p,1/2))$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L150) |
| `Occil.FactoryExtra.powerSeriesHazards` | $\mathrm{Bern}\!\left(1-\sum_{n\ge0}c_n(1-p)^{n+1}\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L50) |

### Bernoulli factories / Trigonometric (10)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.FactoryExtra.alternatingPermutation` | $\mathrm{Bern}\!\left(\begin{cases}(1-p)/\cos p&r=0\\(1-p)\tan p&r=1\end{cases}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L47) |
| `Occil.FactoryExtra.arcsineHalf` | $\mathrm{Bern}\!\left(\frac12\arcsin p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L81) |
| `Occil.FactoryExtra.arcsinePlusSqrtMinusOne` | $\mathrm{Bern}\!\left(\arcsin p+\sqrt{1-p^2}-1\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L69) |
| `Occil.FactoryExtra.arctanOverPi` | $\mathrm{Bern}\!\left(\arctan(p)/\pi\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L32) |
| `Occil.FactoryExtra.complementOverCosine` | $\mathrm{Bern}\!\left(\frac{1-p}{\cos p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L61) |
| `Occil.FactoryExtra.complementTimesTangent` | $\mathrm{Bern}\!\left((1-p)\tan p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L64) |
| `Occil.FactoryExtra.cosineSqrt` | $\mathrm{Bern}\!\left(\cos\sqrt p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L26) |
| `Occil.FactoryExtra.pOverTangent` | $\mathrm{Bern}\!\left(\frac p{\tan p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L88) |
| `Occil.FactoryExtra.sincScaled` | $\mathrm{Bern}\!\left(\frac{\sin(p\sqrt c)}{p\sqrt c}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L17) |
| `Occil.FactoryExtra.sincSqrtScaled` | $\mathrm{Bern}\!\left(\frac{\sin\sqrt{cp}}{\sqrt{cp}}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L37) |

### Constant coins / Engines (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Constants.continuedLogarithm` | $\mathrm{Bern}\!\left(\cfrac{2^{-c_1}}{1+\cfrac{2^{-c_2}}{1+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L118) |
| `Occil.Constants.rationalContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1/d_1}{a_1/d_1+\cfrac{b_2/d_2}{a_2/d_2+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L98) |

### Constant coins / Exponential (9)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Constants.eContinuedFraction` | $\mathrm{Bern}(p_j),\ p_j\text{ a continued-fraction tail}$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L76) |
| `Occil.Constants.eDivThree` | $\mathrm{Bern}\!\left(e/3\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L44) |
| `Occil.Constants.eMinusTwo` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L27) |
| `Occil.Constants.eMinusTwoContinuedFraction` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L89) |
| `Occil.Constants.eQuarter` | $\mathrm{Bern}(e/4)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L131) |
| `Occil.Constants.inverseEPlus` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L53) |
| `Occil.Constants.inverseEPlusContinuedFraction` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L86) |
| `Occil.Constants.tanhHalf` | $\mathrm{Bern}\!\left(\tanh(1/2)\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L93) |
| `Occil.Constants.threeMinusE` | $\mathrm{Bern}\!\left(3-e\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L46) |

### Constant coins / Pi (10)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Constants.arctanRationalOverRatio` | $\mathrm{Bern}(\arctan(x/y)/(x/y))$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L94) |
| `Occil.Constants.fourOverThreePi` | $\mathrm{Bern}\!\left(4/(3\pi)\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L82) |
| `Occil.Constants.inversePi` | $\mathrm{Bern}\!\left(1/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L80) |
| `Occil.Constants.inverseSqrtPi` | $\mathrm{Bern}\!\left(1/\sqrt\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L91) |
| `Occil.Constants.logPiOverPi` | $\mathrm{Bern}\!\left(\log\pi/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L85) |
| `Occil.Constants.piMinusThree` | $\mathrm{Bern}\!\left(\pi-3\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L66) |
| `Occil.Constants.piMinusThreeOverFour` | $\mathrm{Bern}\!\left((\pi-3)/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L64) |
| `Occil.Constants.piQuarter` | $\mathrm{Bern}\!\left(\pi/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L58) |
| `Occil.Constants.piQuarterMinusHalf` | $\mathrm{Bern}\!\left(\pi/4-1/2\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L62) |
| `Occil.Constants.piTwelfth` | $\mathrm{Bern}\!\left(\pi/12\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L60) |

### Constant coins / Special (6)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Constants.erfRatio` | $\mathrm{Bern}(\mathrm{erf}(x)/\mathrm{erf}(1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L76) |
| `Occil.Constants.eulerMascheroni` | $\mathrm{Bern}\!\left(\gamma\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L39) |
| `Occil.Constants.logOnePlusRational` | $\mathrm{Bern}\!\left(\log(1+x/y)\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L49) |
| `Occil.Constants.lowerGammaIntegerRatio` | $\mathrm{Bern}(\gamma(m,x)/\gamma(m,1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L88) |
| `Occil.Constants.rationalIntegerPower` | $\mathrm{Bern}\!\left((a/b)^n\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L53) |
| `Occil.Constants.zetaRelated` | $\mathrm{Bern}\!\left(\zeta(k)(1-2^{1-k})\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L25) |

### Discrete distributions / Binomial (1)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.DiscreteExtra.binomialHalfRejection` | $\mathrm{Bin}(n,1/2)$ | [Binomial.lean](../code/Samplers/Discrete/Binomial.lean#L29) |

### Discrete distributions / Counts (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.DiscreteExtra.betaNegativeBinomial` | $\mathrm{BetaNegBin}(r,\alpha,\beta)$ | [Counts.lean](../code/Samplers/Discrete/Counts.lean#L48) |
| `Occil.DiscreteExtra.inversePolya` | $\mathrm{InversePolya}(r,a,b,c)$ | [Counts.lean](../code/Samplers/Discrete/Counts.lean#L39) |
| `Occil.DiscreteExtra.polyaRational` | $\mathrm{NegBin}(r,p)$ | [Counts.lean](../code/Samplers/Discrete/Counts.lean#L21) |
| `Occil.DiscreteExtra.waringYule` | $\mathrm{BetaNegBin}(1,\alpha,\beta)$ | [Counts.lean](../code/Samplers/Discrete/Counts.lean#L57) |
| `Occil.DiscreteExtra.yuleSimon` | $\mathrm{YuleSimon}(\rho)$ | [Counts.lean](../code/Samplers/Discrete/Counts.lean#L62) |

### Discrete distributions / Tails (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.DiscreteExtra.generalizedGeometric` | $\Pr(K=k)=(1-\rho_k)\prod_{j<k}\rho_j$ | [Tails.lean](../code/Samplers/Discrete/Tails.lean#L96) |
| `Occil.DiscreteExtra.generalizedSibuya` | $\Pr(K=k)=\frac{\alpha}{\nu+k}\prod_{j<k}\left(1-\frac\alpha{\nu+j}\right)$ | [Tails.lean](../code/Samplers/Discrete/Tails.lean#L102) |
| `Occil.DiscreteExtra.rationalPowerCoin` | $\mathrm{Bern}(p^{a/b})$ | [Tails.lean](../code/Samplers/Discrete/Tails.lean#L21) |
| `Occil.DiscreteExtra.zeta` | $\Pr(K=k)=k^{-s}/\zeta(s)$ | [Tails.lean](../code/Samplers/Discrete/Tails.lean#L80) |
| `Occil.DiscreteExtra.zipf` | $\Pr(K=k)\propto k^{-s},\ 1\le k\le n$ | [Tails.lean](../code/Samplers/Discrete/Tails.lean#L68) |

### General sampling / Core (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.General.incompleteInformation` | $\mathrm{Cat}(p)$ | [Core.lean](../code/Samplers/General/Core.lean#L188) |
| `Occil.General.markovStep` | $K(x,\cdot)$ | [Core.lean](../code/Samplers/General/Core.lean#L203) |
| `Occil.General.refinedCDFComparison` | $\mathrm{Bern}(F(x))$ | [Core.lean](../code/Samplers/General/Core.lean#L173) |
| `Occil.General.refinedCoin` | $\mathrm{Bern}(p)$ | [Core.lean](../code/Samplers/General/Core.lean#L157) |
| `Occil.General.shapeRejection` | $\mu(\cdot\mid A)$ | [Core.lean](../code/Samplers/General/Core.lean#L97) |

### Integer and weighted sampling / Aliases (1)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.WeightedVariants.voseDraw` | $\mathrm{Cat}(w)$ | [Aliases.lean](../code/Samplers/Weighted/Aliases.lean#L57) |

### Integer and weighted sampling / Optimal (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.WeightedVariants.optimalChoice` | $\mathrm{Cat}(w)$ | [Optimal.lean](../code/Samplers/Weighted/Optimal.lean#L72) |
| `Occil.WeightedVariants.optimalDraw` | $\mathrm{Cat}(w)$ | [Optimal.lean](../code/Samplers/Weighted/Optimal.lean#L52) |

### Integer and weighted sampling / Rejection (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.WeightedVariants.sortedChoice` | $\mathrm{Cat}(w)$ | [Rejection.lean](../code/Samplers/Weighted/Rejection.lean#L17) |
| `Occil.WeightedVariants.succinctChoice` | $\mathrm{Cat}(w)$ | [Rejection.lean](../code/Samplers/Weighted/Rejection.lean#L53) |

### Integer and weighted sampling / Reservoir (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Weighted.inclusionSplitting` | $\lvert S\rvert=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | [Reservoir.lean](../code/Samplers/Weighted/Reservoir.lean#L44) |
| `Occil.Weighted.inclusionSystematic` | $\lvert S\rvert=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | [Reservoir.lean](../code/Samplers/Weighted/Reservoir.lean#L86) |

### Integer and weighted sampling / Trees (3)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Weighted.fastLoadedDiceRoller` | $\mathrm{Cat}(w)$ | [Trees.lean](../code/Samplers/Weighted/Trees.lean#L47) |
| `Occil.Weighted.hanHoshi` | $\mathrm{Cat}(w)$ | [Trees.lean](../code/Samplers/Weighted/Trees.lean#L73) |
| `Occil.Weighted.knuthYao` | $\mathrm{Cat}(w)$ | [Trees.lean](../code/Samplers/Weighted/Trees.lean#L28) |

### Integer and weighted sampling / Uniform (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.Weighted.recycledSamples` | $\mathrm{Unif}\{0,\ldots,n-1\}^{\otimes k}$ | [Uniform.lean](../code/Samplers/Weighted/Uniform.lean#L71) |
| `Occil.Weighted.recycledUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [Uniform.lean](../code/Samplers/Weighted/Uniform.lean#L53) |

### Lazy coin factories (3)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.arctanFactory` | $\mathrm{Bern}\!\left(\arctan(p)\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L111) |
| `Occil.arctanOverPFactory` | $\mathrm{Bern}\!\left(\arctan(p)/p\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L103) |
| `Occil.sampleGeometricBag` | $\mathrm{Bern}(U)\ \text{with shared latent }U$ | [Lazy.lean](../code/Samplers/Lazy.lean#L53) |

### Lazy exact reals / BetaGamma (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.newBeta` | $\mathsf{Lazy}[\mathrm{Beta}(a,b)]$ | [BetaGamma.lean](../code/Samplers/PSRN/BetaGamma.lean#L20) |
| `Occil.PSRN.newGamma` | $\mathsf{Lazy}[\mathrm{Gamma}(a,b)]$ | [BetaGamma.lean](../code/Samplers/PSRN/BetaGamma.lean#L80) |
| `Occil.PSRN.newGammaInteger` | $\mathsf{Lazy}[\mathrm{Gamma}(k,\lambda)]$ | [BetaGamma.lean](../code/Samplers/PSRN/BetaGamma.lean#L60) |
| `Occil.PSRN.newGammaMixture` | $\mathsf{Lazy}[\text{Gamma mixture}]$ | [BetaGamma.lean](../code/Samplers/PSRN/BetaGamma.lean#L67) |
| `Occil.PSRN.newLindley` | $\mathsf{Lazy}[\mathrm{Lindley}]$ | [BetaGamma.lean](../code/Samplers/PSRN/BetaGamma.lean#L73) |

### Lazy exact reals / Core (4)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.coin` | $\mathrm{Bern}(x)\ \text{conditional on cached }x$ | [Core.lean](../code/Samplers/PSRN/Core.lean#L100) |
| `Occil.PSRN.newInsideShape` | $\mathsf{Lazy}[\mathrm{Unif}(A)]$ | [Core.lean](../code/Samplers/PSRN/Core.lean#L105) |
| `Occil.PSRN.newRejection` | $\mathsf{Lazy}[\mu(\cdot\mid A)]$ | [Core.lean](../code/Samplers/PSRN/Core.lean#L93) |
| `Occil.PSRN.newUniform` | $\mathsf{Lazy}[\mathrm{Unif}(0,1)]$ | [Core.lean](../code/Samplers/PSRN/Core.lean#L43) |

### Lazy exact reals / Distributions (16)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.newArcCosine` | $\mathsf{Lazy}[\text{Arc Cosine}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L82) |
| `Occil.PSRN.newCauchy` | $\mathsf{Lazy}[\mathrm{Cauchy}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L24) |
| `Occil.PSRN.newContinuousBernoulli` | $\mathsf{Lazy}[\text{Continuous Bernoulli}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L35) |
| `Occil.PSRN.newEpanechnikov` | $\mathsf{Lazy}[\mathrm{Epanechnikov}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L48) |
| `Occil.PSRN.newFGMCopula` | $\mathsf{Lazy}[\mathrm{FGMCopula}(\theta)]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L55) |
| `Occil.PSRN.newGarima` | $\mathsf{Lazy}[\mathrm{Garima}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L125) |
| `Occil.PSRN.newHyperbolicSecant` | $\mathsf{Lazy}[\text{Hyperbolic Secant}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L71) |
| `Occil.PSRN.newIGarima` | $\mathsf{Lazy}[\text{I Garima}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L128) |
| `Occil.PSRN.newMirra` | $\mathsf{Lazy}[\mathrm{Mirra}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L137) |
| `Occil.PSRN.newRayleigh` | $\mathsf{Lazy}[\mathrm{Rayleigh}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L18) |
| `Occil.PSRN.newRectellipse` | $\mathsf{Lazy}[\mathrm{Rectellipse}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L153) |
| `Occil.PSRN.newSushila` | $\mathsf{Lazy}[\mathrm{Sushila}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L142) |
| `Occil.PSRN.newTulap` | $\mathsf{Lazy}[\mathrm{Tulap}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L103) |
| `Occil.PSRN.newWeightedExponentialGamma` | $\mathsf{Lazy}[\text{Weighted Exponential Gamma}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L131) |
| `Occil.PSRN.newXLindley` | $\mathsf{Lazy}[\text{X Lindley}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L147) |
| `Occil.PSRN.newXgamma` | $\mathsf{Lazy}[\mathrm{Xgamma}]$ | [Distributions.lean](../code/Samplers/PSRN/Distributions.lean#L134) |

### Lazy exact reals / Exponential (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.expMinusCoin` | $\mathrm{Bern}\!\left(e^{-x}\right)$ | [Exponential.lean](../code/Samplers/PSRN/Exponential.lean#L53) |
| `Occil.PSRN.newExponential` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | [Exponential.lean](../code/Samplers/PSRN/Exponential.lean#L32) |
| `Occil.PSRN.newExponentialFromDecay` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | [Exponential.lean](../code/Samplers/PSRN/Exponential.lean#L19) |
| `Occil.PSRN.newExponentialLogRate` | $\mathsf{Lazy}[\mathrm{Exp}(\log(x/y))]$ | [Exponential.lean](../code/Samplers/PSRN/Exponential.lean#L39) |
| `Occil.PSRN.newExponentialUnknownRate` | $\mathsf{Lazy}[\mathrm{Exp}(p)]$ | [Exponential.lean](../code/Samplers/PSRN/Exponential.lean#L46) |

### Lazy exact reals / Gaussian (2)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.newGaussian` | $\mathsf{Lazy}[\mathcal N(0,1)]$ | [Gaussian.lean](../code/Samplers/PSRN/Gaussian.lean#L31) |
| `Occil.PSRN.newNormal` | $\mathsf{Lazy}[\mathcal N(\mu,\sigma^2)]$ | [Gaussian.lean](../code/Samplers/PSRN/Gaussian.lean#L46) |

### Lazy exact reals / Geometry (5)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.newBall` | $\mathsf{Lazy}[\mathrm{Unif}(B^d)]$ | [Geometry.lean](../code/Samplers/PSRN/Geometry.lean#L45) |
| `Occil.PSRN.newDirichlet` | $\mathsf{Lazy}[\mathrm{Dirichlet}(\alpha)]$ | [Geometry.lean](../code/Samplers/PSRN/Geometry.lean#L68) |
| `Occil.PSRN.newShell` | $\mathsf{Lazy}[\mathrm{Unif}(\text{spherical shell})]$ | [Geometry.lean](../code/Samplers/PSRN/Geometry.lean#L54) |
| `Occil.PSRN.newSimplex` | $\mathsf{Lazy}[\mathrm{Unif}(\Delta_d)]$ | [Geometry.lean](../code/Samplers/PSRN/Geometry.lean#L91) |
| `Occil.PSRN.newSphere` | $\mathsf{Lazy}[\mathrm{Unif}(S^{d-1})]$ | [Geometry.lean](../code/Samplers/PSRN/Geometry.lean#L34) |

### Lazy exact reals / Uniform (9)

| Entry | Intended law | Code |
| --- | --- | --- |
| `Occil.PSRN.newByDigits` | $\mathsf{Lazy}[\text{digit-oracle real}]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L52) |
| `Occil.PSRN.newOddsUniform` | $\mathsf{Lazy}[U/(1-U)]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L87) |
| `Occil.PSRN.newOrderStatistic` | $\mathsf{Lazy}[\mathrm{Beta}(k,n+1-k)]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L19) |
| `Occil.PSRN.newPowerUniform` | $\mathsf{Lazy}[U^{a/b}]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L32) |
| `Occil.PSRN.newRatioUniforms` | $\mathsf{Lazy}[U/V]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L77) |
| `Occil.PSRN.newReciprocalPowerUniform` | $\mathsf{Lazy}[U^{-a/b}]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L83) |
| `Occil.PSRN.newReciprocalUniform` | $\mathsf{Lazy}[1/U]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L80) |
| `Occil.PSRN.newUniformSum` | $\mathsf{Lazy}[\sum_{i=1}^nU_i]$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L72) |
| `Occil.PSRN.powerCoin` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Uniform.lean](../code/Samplers/PSRN/Uniform.lean#L39) |

## Additional grid/numerical exclusions

These 11 are not included in the 137, despite their General sampling catalogue groups.

- `Occil.General.bestCandidate`
- `Occil.General.farthestPoints`
- `Occil.General.gaussianKernelDensity`
- `Occil.General.gaussianKernelDensityVector`
- `Occil.General.gaussianMixture`
- `Occil.General.linearRegression`
- `Occil.General.poissonDiskRejection`
- `Occil.General.sliceSamplerStepOut`
- `Occil.General.sliceStepOut`
- `Occil.General.stochasticInterpolation`
- `Occil.General.stratifiedCell`
