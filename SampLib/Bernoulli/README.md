# Bernoulli

Coin composition and Bernoulli factories: linear, rational, series, polynomial and envelope.

Part of the [library layout](../README.md#layout).

## Verified samplers (100)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.FactoryExtra.addition` | $\mathrm{Bern}\!\left(p+q\right)$ | [Addition](Addition.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L63) |
| `Occil.FactoryExtra.affine` | $\mathrm{Bern}\!\left(\frac{d+p}{c}\right)$ | [AffineFactory](AffineFactory.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L27) |
| `Occil.FactoryExtra.affineRatio` | $\mathrm{Bern}\!\left(\frac{d+q}{c+p}\right)$ | [AffineRatio](AffineRatio.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L36) |
| `Occil.FactoryExtra.alternatingPermutation` | $\mathrm{Bern}\!\left(\begin{cases}(1-p)/\cos p&r=0\\(1-p)\tan p&r=1\end{cases}\right)$ | [AlternatingPermutation](AlternatingPermutation.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L47) |
| `Occil.FactoryExtra.alternatingSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}(-1)^nc_np^n\right)$ | [AlternatingSeries](AlternatingSeries.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L20) |
| `Occil.FactoryExtra.approximateFactory` | $\mathrm{Bern}\!\left(\mathbb E[\mathrm{clip}(f_s(\lfloor sK/N\rfloor),0,s)/s]\right)$ | [ApproximateFactory](ApproximateFactory.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L125) |
| `Occil.FactoryExtra.arcsineHalf` | $\mathrm{Bern}\!\left(\frac12\arcsin p\right)$ | [ArcsineFactories](ArcsineFactories.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L81) |
| `Occil.FactoryExtra.arcsinePlusSqrtMinusOne` | $\mathrm{Bern}\!\left(\arcsin p+\sqrt{1-p^2}-1\right)$ | [ArcsineFactories](ArcsineFactories.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L69) |
| `Occil.FactoryExtra.arctanOverPi` | $\mathrm{Bern}\!\left(\arctan(p)/\pi\right)$ | [ArctanOverPi](ArctanOverPi.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L32) |
| `Occil.FactoryExtra.binaryExponential` | $\mathrm{Bern}\!\left(2^{-m(k+p)}\right)$ | [BinaryExponential](BinaryExponential.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L88) |
| `Occil.FactoryExtra.binaryExponentialRational` | $\mathrm{Bern}\!\left(2^{-ap/b}\right)$ | [BinaryExponentialRational](BinaryExponentialRational.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L98) |
| `Occil.FactoryExtra.complementHalf` | $\mathrm{Bern}\!\left(\frac{1-p}{2}\right)$ | [ComplementHalf](ComplementHalf.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L124) |
| `Occil.FactoryExtra.complementLogInverse` | $\mathrm{Bern}\!\left((1-p)\log(1/(1-p))\right)$ | [ComplementLogInverse](ComplementLogInverse.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L97) |
| `Occil.FactoryExtra.complementLogOnePlus` | $\mathrm{Bern}(1-\log(1+p))$ | [ComplementLogOnePlus](ComplementLogOnePlus.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L128) |
| `Occil.FactoryExtra.complementOverCosine` | $\mathrm{Bern}\!\left(\frac{1-p}{\cos p}\right)$ | [AlternatingPermutation](AlternatingPermutation.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L61) |
| `Occil.FactoryExtra.complementOverLogInverse` | $\mathrm{Bern}\!\left(\frac{1-p}{\log(1/p)}\right)$ | [LogRatioFactories](LogRatioFactories.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L107) |
| `Occil.FactoryExtra.complementPowerSeries` | $\mathrm{Bern}\!\left(1-\frac{\sum_i c_i(1-p)^{i+1}}{\sum_i c_i}\right)$ | [ComplementPowerSeries](ComplementPowerSeries.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L42) |
| `Occil.FactoryExtra.complementTimesTangent` | $\mathrm{Bern}\!\left((1-p)\tan p\right)$ | [AlternatingPermutation](AlternatingPermutation.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L64) |
| `Occil.FactoryExtra.convexCombination` | $\mathrm{Bern}\!\left(\frac{\sum_iw_ip_i}{\sum_iw_i}\right)$ | [ConvexCombination](ConvexCombination.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L59) |
| `Occil.FactoryExtra.cosineSqrt` | $\mathrm{Bern}\!\left(\cos\sqrt p\right)$ | [TrigonometricSeriesFactories](TrigonometricSeriesFactories.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L26) |
| `Occil.FactoryExtra.division` | $\mathrm{Bern}\!\left(p/q\right)$ | [Division](Division.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L73) |
| `Occil.FactoryExtra.envelopeFactory` | $\mathrm{Bern}\!\left(f(p)\right)$ | [EnvelopeFactory](EnvelopeFactory.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L118) |
| `Occil.FactoryExtra.envelopeFactoryDegrees` | $\mathrm{Bern}\!\left(f(p)\right)$ | [EnvelopeFactory](EnvelopeFactory.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L79) |
| `Occil.FactoryExtra.epsilonDivision` | $\mathrm{Bern}\!\left(p/q\right)$ | [EpsilonDivision](EpsilonDivision.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L78) |
| `Occil.FactoryExtra.expDivThree` | $\mathrm{Bern}\!\left(e^p/3\right)$ | [ExpDivThree](ExpDivThree.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L65) |
| `Occil.FactoryExtra.expIntegral` | $\mathrm{Bern}\!\left(\frac{1-e^{-(m+p)}}{m+p}\right)$ | [ExpIntegral](ExpIntegral.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L71) |
| `Occil.FactoryExtra.expMinusExp` | $\mathrm{Bern}\!\left(e^{-e^{m+p}}\right)$ | [ExpMinusExp](ExpMinusExp.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L72) |
| `Occil.FactoryExtra.expMinusPolynomial` | $\mathrm{Bern}\!\left(e^{-\sum_i a_ip^i}\right)$ | [ExpMinusPolynomial](ExpMinusPolynomial.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L39) |
| `Occil.FactoryExtra.expMinusScaled` | $\mathrm{Bern}\!\left(e^{-cp}\right)$ | [ExpMinusScaled](ExpMinusScaled.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L17) |
| `Occil.FactoryExtra.expMinusShiftPower` | $\mathrm{Bern}\!\left(e^{-(m+p)^k}\right)$ | [ExpMinusShiftPower](ExpMinusShiftPower.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L52) |
| `Occil.FactoryExtra.expMinusShifted` | $\mathrm{Bern}\!\left(e^{-(m+p)}\right)$ | [ExpMinusShifted](ExpMinusShifted.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L23) |
| `Occil.FactoryExtra.expSquareTimesComplement` | $\mathrm{Bern}\!\left(e^{p^2}(1-p)\right)$ | [ExpSquareTimesComplement](ExpSquareTimesComplement.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L82) |
| `Occil.FactoryExtra.expTimesComplement` | $\mathrm{Bern}\!\left(e^p(1-p)\right)$ | [ExpTimesComplement](ExpTimesComplement.lean) | [Exponential.lean](../../code/Samplers/Bernoulli/Exponential.lean#L28) |
| `Occil.FactoryExtra.exponentialRatio` | $\mathrm{Bern}\!\left(\frac{1+e^{z-w}}{1+e^z}\right)$ | [ExponentialRatio](ExponentialRatio.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L66) |
| `Occil.FactoryExtra.exponentialTwist` | $\mathrm{Bern}\!\left(\frac{pe^z}{pe^z+1-p}\right)$ | [ExponentialTwist](ExponentialTwist.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L58) |
| `Occil.FactoryExtra.gambler` | $\mathrm{Bern}\!\left(\frac{\sum_{j=1}^{h-1}(cp)^j}{\sum_{j=0}^{h-1}(cp)^j}\right)$ | [Gambler](Gambler.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L16) |
| `Occil.FactoryExtra.highPowerLogistic` | $\mathrm{Bern}\!\left(\frac{(cp)^m}{\sum_{j=0}^m(cp)^j}\right)$ | [HighPowerLogistic](HighPowerLogistic.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L25) |
| `Occil.FactoryExtra.integralMixture` | $\mathrm{Bern}\!\left(\int f(x)\,\mu(dx)\right)$ | [IntegralMixture](IntegralMixture.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L67) |
| `Occil.FactoryExtra.inverseQuadratic` | $\mathrm{Bern}\!\left(\frac1{1+(m+p)^2}\right)$ | [InverseQuadratic](InverseQuadratic.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L68) |
| `Occil.FactoryExtra.linear` | $\mathrm{Bern}\!\left(cp\right)$ | [LinearFactory](LinearFactory.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L35) |
| `Occil.FactoryExtra.linear2014` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear2014](Linear2014.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L129) |
| `Occil.FactoryExtra.linearLowProbability` | $\mathrm{Bern}\!\left(cp\right)$ | [LinearLowProbability](LinearLowProbability.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L93) |
| `Occil.FactoryExtra.linearPower` | $\mathrm{Bern}\!\left((cp)^m\right)$ | [LinearPower](LinearPower.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L57) |
| `Occil.FactoryExtra.linearPowerWalk` | $\mathrm{Bern}\!\left((cp)^m\right)$ | [LinearPowerWalk](LinearPowerWalk.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L108) |
| `Occil.FactoryExtra.logOverAffine` | $\mathrm{Bern}\!\left(\frac{\log(c+p)}{c+p}\right)$ | [LogOverAffine](LogOverAffine.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L83) |
| `Occil.FactoryExtra.logisticExp` | $\mathrm{Bern}\!\left(\frac1{1+e^{z/2^k}}\right)$ | [LogisticExp](LogisticExp.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L38) |
| `Occil.FactoryExtra.minimumComplement` | $\mathrm{Bern}\!\left(\min(p,1-p)\right)$ | [MinimumComplement](MinimumComplement.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L135) |
| `Occil.FactoryExtra.minimumHalf` | $\mathrm{Bern}(\min(p,1/2))$ | [MinimumHalf](MinimumHalf.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L150) |
| `Occil.FactoryExtra.oddsProduct` | $\mathrm{Bern}\!\left(\frac{\mu p}{1-\mu+\mu p}\right)$ | [OddsProduct](OddsProduct.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L104) |
| `Occil.FactoryExtra.offsetRace` | $\mathrm{Bern}\!\left(\frac{d+q}{c+p+d+q}\right)$ | [OffsetRace](OffsetRace.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L83) |
| `Occil.FactoryExtra.oneDivTwoMinus` | $\mathrm{Bern}\!\left(\frac1{2-p}\right)$ | [OneDivTwoMinus](OneDivTwoMinus.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L64) |
| `Occil.FactoryExtra.oneMinusOverOnePlus` | $\mathrm{Bern}\!\left(\frac{1-p}{1+p}\right)$ | [OneMinusOverOnePlus](OneMinusOverOnePlus.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L16) |
| `Occil.FactoryExtra.onePlusHalf` | $\mathrm{Bern}\!\left(\frac{1+p}{2}\right)$ | [OnePlusHalf](OnePlusHalf.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L120) |
| `Occil.FactoryExtra.pLogInverse` | $\mathrm{Bern}\!\left(p\log(1/p)\right)$ | [PLogInverse](PLogInverse.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L91) |
| `Occil.FactoryExtra.pOverLogInverseComplement` | $\mathrm{Bern}\!\left(\frac p{\log(1/(1-p))}\right)$ | [LogRatioFactories](LogRatioFactories.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L101) |
| `Occil.FactoryExtra.pOverTangent` | $\mathrm{Bern}\!\left(\frac p{\tan p}\right)$ | [POverTangent](POverTangent.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L88) |
| `Occil.FactoryExtra.polylogarithm` | $\mathrm{Bern}\!\left(\mathrm{Li}_r(p)(1/p-1)\right)$ | [Polylogarithm](Polylogarithm.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L113) |
| `Occil.FactoryExtra.polynomial` | $\mathrm{Bern}\!\left(f(p)\right)$ | [PolynomialFactory](PolynomialFactory.lean) | [Polynomials.lean](../../code/Samplers/Bernoulli/Polynomials.lean#L19) |
| `Occil.FactoryExtra.positivePowerSeries` | $\mathrm{Bern}\!\left(\frac{\sum_i c_ip^i}{\sum_i c_i}\right)$ | [PositivePowerSeries](PositivePowerSeries.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L36) |
| `Occil.FactoryExtra.powerSeriesHazards` | $\mathrm{Bern}\!\left(1-\sum_{n\ge0}c_n(1-p)^{n+1}\right)$ | [PowerSeriesHazards](PowerSeriesHazards.lean) | [Series.lean](../../code/Samplers/Bernoulli/Series.lean#L50) |
| `Occil.FactoryExtra.rationalFunction` | $\mathrm{Bern}\!\left(f(p)/g(p)\right)$ | [RationalFunction](RationalFunction.lean) | [Polynomials.lean](../../code/Samplers/Bernoulli/Polynomials.lean#L48) |
| `Occil.FactoryExtra.reciprocalAffine` | $\mathrm{Bern}\!\left(\frac d{c+p}\right)$ | [ReciprocalAffine](ReciprocalAffine.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L15) |
| `Occil.FactoryExtra.reciprocalAffinePower` | $\mathrm{Bern}\!\left(\left(\frac d{c+p}\right)^k\right)$ | [ReciprocalAffinePower](ReciprocalAffinePower.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L77) |
| `Occil.FactoryExtra.reciprocalExpAffine` | $\mathrm{Bern}\!\left(\frac1{c+e^{-z}}\right)$ | [ReciprocalExpAffine](ReciprocalExpAffine.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L99) |
| `Occil.FactoryExtra.reciprocalLogistic` | $\mathrm{Bern}\!\left(\frac1{1+cp}\right)$ | [ReciprocalLogistic](ReciprocalLogistic.lean) | [Rational.lean](../../code/Samplers/Bernoulli/Rational.lean#L60) |
| `Occil.FactoryExtra.sigmoidDerivative` | $\mathrm{Bern}\!\left(\sigma(z)(1-\sigma(z))\right)$ | [SigmoidDerivative](SigmoidDerivative.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L132) |
| `Occil.FactoryExtra.sigmoidRational` | $\mathrm{Bern}\!\left(\frac1{1+e^{-a/b}}\right)$ | [SigmoidRational](SigmoidRational.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L23) |
| `Occil.FactoryExtra.sigmoidScaled` | $\mathrm{Bern}\!\left(\frac1{1+e^{-ap/b}}\right)$ | [SigmoidScaled](SigmoidScaled.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L31) |
| `Occil.FactoryExtra.sincScaled` | $\mathrm{Bern}\!\left(\frac{\sin(p\sqrt c)}{p\sqrt c}\right)$ | [TrigonometricSeriesFactories](TrigonometricSeriesFactories.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L17) |
| `Occil.FactoryExtra.sincSqrtScaled` | $\mathrm{Bern}\!\left(\frac{\sin\sqrt{cp}}{\sqrt{cp}}\right)$ | [TrigonometricSeriesFactories](TrigonometricSeriesFactories.lean) | [Trigonometric.lean](../../code/Samplers/Bernoulli/Trigonometric.lean#L37) |
| `Occil.FactoryExtra.subtraction` | $\mathrm{Bern}\!\left(p-q\right)$ | [Subtraction](Subtraction.lean) | [Linear.lean](../../code/Samplers/Bernoulli/Linear.lean#L68) |
| `Occil.FactoryExtra.tanhHalfShifted` | $\mathrm{Bern}\!\left(\tanh((m+p)/2)\right)$ | [TanhHalfShifted](TanhHalfShifted.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L53) |
| `Occil.FactoryExtra.tanhRational` | $\mathrm{Bern}\!\left(\tanh(a/b)\right)$ | [TanhRational](TanhRational.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L43) |
| `Occil.FactoryExtra.tanhScaled` | $\mathrm{Bern}\!\left(\tanh(ap/b)\right)$ | [TanhScaled](TanhScaled.lean) | [Elementary.lean](../../code/Samplers/Bernoulli/Elementary.lean#L48) |
| `Occil.FactoryExtra.threePointPiecewise` | $\mathrm{Bern}(f(p)),\ f\text{ piecewise affine}$ | [ThreePointPiecewise](ThreePointPiecewise.lean) | [Polynomials.lean](../../code/Samplers/Bernoulli/Polynomials.lean#L57) |
| `Occil.FactoryExtra.twoCoin` | $\mathrm{Bern}\!\left(\frac{\beta xp}{\beta(xp+yq)+(1-\beta)(x+y)}\right)$ | [TwoCoin](TwoCoin.lean) | [Powers.lean](../../code/Samplers/Bernoulli/Powers.lean#L35) |
| `Occil.FactoryExtra.twoCoinPower` | $\mathrm{Bern}\!\left(p^q\right)$ | [TwoCoinPower](TwoCoinPower.lean) | [Powers.lean](../../code/Samplers/Bernoulli/Powers.lean#L24) |
| `Occil.arctanFactory` | $\mathrm{Bern}\!\left(\arctan(p)\right)$ | [ArctanFactory](ArctanFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L111) |
| `Occil.arctanOverPFactory` | $\mathrm{Bern}\!\left(\arctan(p)/p\right)$ | [ArctanOverPFactory](ArctanOverPFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L103) |
| `Occil.bernoulliRace` | $\mathrm{Bern}\!\left(\frac{p}{p+q}\right)$ | [BernoulliRace](BernoulliRace.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L33) |
| `Occil.bernsteinFactory` | $\mathrm{Bern}\!\left(\sum_{k=0}^n c_k\binom nk p^k(1-p)^{n-k}\right)$ | [BernsteinFactory](BernsteinFactory.lean) | [Combinators.lean](../../code/Samplers/Bernoulli/Combinators.lean#L26) |
| `Occil.coinConditional` | $\mathrm{Bern}\!\left(rp+(1-r)q\right)$ | [CoinConditional](CoinConditional.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L22) |
| `Occil.coinDisjunction` | $\mathrm{Bern}\!\left(p+q-pq\right)$ | [CoinDisjunction](CoinDisjunction.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L16) |
| `Occil.coinMean` | $\mathrm{Bern}\!\left(\frac{p+q}{2}\right)$ | [CoinMean](CoinMean.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L19) |
| `Occil.coinProduct` | $\mathrm{Bern}\!\left(pq\right)$ | [CoinProduct](CoinProduct.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L13) |
| `Occil.complement` | $\mathrm{Bern}\!\left(1-p\right)$ | [Complement](Complement.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L11) |
| `Occil.cosineFactory` | $\mathrm{Bern}\!\left(\cos(p)\right)$ | [CosineFactory](CosineFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L86) |
| `Occil.evenParity` | $\mathrm{Bern}\!\left(\frac1{1+p}\right)$ | [EvenParity](EvenParity.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L44) |
| `Occil.expMinusFactory` | $\mathrm{Bern}\!\left(e^{-p}\right)$ | [ExpMinusFactory](ExpMinusFactory.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L74) |
| `Occil.expMinusMartingale` | $\mathrm{Bern}\!\left(e^{-p}\right)$ | [ExpMinusMartingale](ExpMinusMartingale.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L83) |
| `Occil.expMinusRational` | $\mathrm{Bern}\!\left(e^{-x/y}\right)$ | [ExpMinusRational](ExpMinusRational.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L60) |
| `Occil.factorialSeriesFactory` | $\mathrm{Bern}(e^{-p}),\ \mathrm{Bern}(\cos p),\ \mathrm{Bern}(\sin(p)/p)$ | [FactorialSeriesFactory](FactorialSeriesFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L62) |
| `Occil.fractionalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [FractionalPower](FractionalPower.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L51) |
| `Occil.logOnePlusFactory` | $\mathrm{Bern}\!\left(\log(1+p)\right)$ | [LogOnePlusFactory](LogOnePlusFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L94) |
| `Occil.logisticFactory` | $\mathrm{Bern}\!\left(\frac{xp}{y+xp}\right)$ | [LogisticFactory](LogisticFactory.lean) | [Combinators.lean](../../code/Samplers/Bernoulli/Combinators.lean#L12) |
| `Occil.oneDivOnePlus` | $\mathrm{Bern}\!\left(\frac1{1+p}\right)$ | [OneDivOnePlus](OneDivOnePlus.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L39) |
| `Occil.probabilityGeneratingFactory` | $\mathrm{Bern}\!\left(\mathbb E[p^N]\right)$ | [ProbabilityGeneratingFactory](ProbabilityGeneratingFactory.lean) | [Combinators.lean](../../code/Samplers/Bernoulli/Combinators.lean#L19) |
| `Occil.sampleGeometricBag` | $\mathrm{Bern}(U)\ \text{with shared latent }U$ | [SampleGeometricBag](SampleGeometricBag.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L53) |
| `Occil.sineFactory` | $\mathrm{Bern}\!\left(\sin(p)\right)$ | [SineFactory](SineFactory.lean) | [Lazy.lean](../../code/Samplers/Lazy.lean#L89) |
| `Occil.vonNeumann` | $\mathrm{Bern}\!\left(\frac12\right)$ | [VonNeumann](VonNeumann.lean) | [Basic.lean](../../code/Samplers/Bernoulli/Basic.lean#L26) |

## Contents

- 97 top-level modules
- [`Laws/`](Laws): 80 modules, target laws, kernels and expectation lemmas
- [`Syntax/`](Syntax): 15 modules, unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 38 modules, CTE loop invariants and program-level helpers

---

Generated by `python3 agent-scripts/law_index.py`.
