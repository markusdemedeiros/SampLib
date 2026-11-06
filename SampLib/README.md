# Verified sampler suite

216 sampler specifications: 214 new verifications and the two initial examples.
Import `SampLib` for the complete library. Runtime terms remain under `code/Samplers`.

Each proof centers on one expectation-preservation argument and a simple CTE
symbolic-execution proof. The public `*_distSpec` theorem uses
[`IsDistSpec`](Templates.lean): normalized mathematical laws, typed returned values,
and arbitrary measurable ENNReal continuation credits, including infinity.
Callback-based samplers assume callback specs; concrete primitives are proved.
Stateful samplers use [`IsOwnedDistSpec`](OwnedDistSpec.lean) to require and
preserve their representation invariant while providing the same normalized
law and arbitrary continuation credits.
Adequacy corollaries are omitted.

Unless a row states otherwise, coin biases range over the full unit interval.
Finite count laws use the standard independent-trial convolution definitions;
closed-form PMF expansions are not needed by their CTE proofs. Min/max also expose
their order-statistic CDF or survival function.

## Uniform draws and primitive coins

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.realCoin` | Bernoulli(p), p∈[0,1] | [RealCoin](Samplers/RealCoin.lean) |
| `Occil.uniformInt` | Uniform [0,n), n>0 | [UniformInt](Samplers/UniformInt.lean) |
| `Occil.rndInt` | Uniform [0,hi], hi≥0 | [RndInt](Samplers/RndInt.lean) |
| `Occil.rndIntRange` | Uniform signed inclusive interval, lo≤hi | [RndIntRange](Samplers/RndIntRange.lean) |
| `Occil.rndIntExcRange` | Uniform signed half-open interval, lo<hi | [RndIntExcRange](Samplers/RndIntExcRange.lean) |
| `Occil.fairCoin` | Fair Boolean from a uniform integer bit | [FairCoin](Samplers/FairCoin.lean) |
| `Occil.rationalCoin` | Bernoulli(a/b), integer 0≤a≤b and b>0 | [RationalCoin](Samplers/RationalCoin.lean) |

## Coin composition

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.complement` | Bias 1-p | [Complement](Samplers/Complement.lean) |
| `Occil.coinProduct` | Bias pq | [CoinProduct](Samplers/CoinProduct.lean) |
| `Occil.coinDisjunction` | Bias p+q-pq | [CoinDisjunction](Samplers/CoinDisjunction.lean) |
| `Occil.coinMean` | Bias (p+q)/2 | [CoinMean](Samplers/CoinMean.lean) |
| `Occil.coinConditional` | Bias rp+(1-r)q | [CoinConditional](Samplers/CoinConditional.lean) |
| `Occil.FactoryExtra.onePlusHalf` | Bias (1+p)/2 | [OnePlusHalf](Samplers/OnePlusHalf.lean) |
| `Occil.FactoryExtra.complementHalf` | Bias (1-p)/2 | [ComplementHalf](Samplers/ComplementHalf.lean) |

## Finite trials and count distributions

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.iterateCoin` | Bernoulli(p^n), all n≥0 | [IterateCoin](Samplers/IterateCoin.lean) |
| `Occil.binomial` | Sum of n Bernoulli(p) trials, all n≥0 | [Binomial](Samplers/Binomial.lean) |
| `Occil.boundedGeometric` | Failures capped at n, all n≥0 and p∈[0,1] | [BoundedGeometric](Samplers/BoundedGeometric.lean) |
| `Occil.randomWalk` | Sum of n independent symmetric ±1 steps, n≥0 | [RandomWalk](Samplers/RandomWalk.lean) |
| `Occil.geometric` | Failures before success, 0<p≤1 | [Geometric](Samplers/Geometric.lean) |
| `Occil.negativeBinomial` | Failures before r successes; r=0 or p>0 | [NegativeBinomial](Samplers/NegativeBinomial.lean) |
| `Occil.geometricFailures` | z+Geometric(1-p), any integer z and p<1 | [GeometricFailures](Samplers/GeometricFailures.lean) |
| `Occil.dice` | Sum of n independent uniform dice; n≥0, sides>0 | [Dice](Samplers/Dice.lean) |
| `Occil.hypergeometric` | Marked count in n draws without replacement; n≤ones+zeros | [Hypergeometric](Samplers/Hypergeometric.lean) |
| `Occil.polyaEggenberger` | Reinforced-urn count; n=0 or positive initial total, reinforcement≥0 | [PolyaEggenberger](Samplers/PolyaEggenberger.lean) |

## Recursive coin factories

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.vonNeumann` | Fair output from a p-coin, 0<p<1 | [VonNeumann](Samplers/VonNeumann.lean) |
| `Occil.oneDivOnePlus` | Bias 1/(1+p), p∈[0,1] | [OneDivOnePlus](Samplers/OneDivOnePlus.lean) |
| `Occil.evenParity` | Bias 1/(1+p), p<1 | [EvenParity](Samplers/EvenParity.lean) |
| `Occil.bernoulliRace` | Bias p/(p+q), p+q>0 | [BernoulliRace](Samplers/BernoulliRace.lean) |
| `Occil.FactoryExtra.oneMinusOverOnePlus` | Bias (1-p)/(1+p), p∈[0,1] | [OneMinusOverOnePlus](Samplers/OneMinusOverOnePlus.lean) |
| `Occil.logisticFactory` | Bias xp/(y+xp), positive integers x,y; all p | [LogisticFactory](Samplers/LogisticFactory.lean) |
| `Occil.bernsteinFactory` | Bernstein polynomial bias; nonempty list of valid rational coefficients | [BernsteinFactory](Samplers/BernsteinFactory.lean) |
| `Occil.FactoryExtra.pLogInverse` | Bias p·log(1/p), 0<p≤1 | [PLogInverse](Samplers/PLogInverse.lean) |

## Continuous laws and generic sampling schemes

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.uniformMin` | Minimum of two uniforms; survival (1-t)^2 on [0,1] | [UniformMin](Samplers/UniformMin.lean) |
| `Occil.uniformMax` | Maximum of two uniforms; CDF t² on [0,1] | [UniformMax](Samplers/UniformMax.lean) |
| `Occil.uniformSum` | n-fold unit-uniform sum (Irwin–Hall), including n=0 | [UniformSum](Samplers/UniformSum.lean) |
| `Occil.exponential` | Standard unit-rate exponential measure | [Exponential](Samplers/Exponential.lean) |
| `Occil.laplace` | Independent unit-exponential magnitude and fair sign | [Laplace](Samplers/Laplace.lean) |
| `Occil.erlang` | Sum of shape independent unit exponentials; shape>0 | [Erlang](Samplers/Erlang.lean) |
| `Occil.mixture` | pμ+(1-p)ν on any shared encoded output type | [Mixture](Samplers/Mixture.lean) |
| `Occil.rejection` | μ conditioned on measurable A, μ(A)>0, including μ(A)=1 | [Rejection](Samplers/Rejection.lean) |
| `Occil.probabilityGeneratingFactory` | Bias E[p^N], any natural-count law; no moment bound | [ProbabilityGeneratingFactory](Samplers/ProbabilityGeneratingFactory.lean) |

The exponential-family proofs currently specialize to ProbLang over mathematical
reals. Exponential is identified with mathlib's `expMeasure 1`; Laplace and Erlang
use the standard independent-variable constructions, without a Gamma-density
expansion. The definitionally identical upstream decreasing-chain proof is reused
through [DecreasingTrial](Samplers/DecreasingTrial.lean), a supporting helper.

## Weighted and collection sampling

| Sampler | Law and domain | Proof |
| --- | --- | --- |
| `Occil.weightedChoice` | Category probability weight/total; nonnegative integer weights, positive total | [WeightedChoice](Samplers/WeightedChoice.lean) |
| `Occil.weightedRejection` | Same categorical law; positive integer envelope dominates every weight | [WeightedRejection](Samplers/WeightedRejection.lean) |
| `Occil.choice` | Uniform position in a nonempty list; duplicates retain multiplicity | [Choice](Samplers/Choice.lean) |
| `Occil.sampleWithReplacement` | Independent list positions; all n≥0, including empty-input zero draws | [SampleWithReplacement](Samplers/SampleWithReplacement.lean) |
| `Occil.sampleWithoutReplacement` | Uniform ordered distinct positions; 0≤k≤length | [SampleWithoutReplacement](Samplers/SampleWithoutReplacement.lean) |
| `Occil.sampleInOrder` | Uniform position subsets returned in input order; 0≤k≤length | [SampleInOrder](Samplers/SampleInOrder.lean) |

Without-replacement selections preserve position multiplicities when values
coincide. Their probabilities are characterized by falling factorials and binomial
coefficients. The reinforced-urn word law has an explicit rising-product formula;
the Bernstein factory exposes its polynomial bias through a reusable identification
of our binomial law with mathlib's.

<!-- expansion:start -->
## Expansion campaign

Accepted additions to the original 47-sampler suite. The [law index](../LAWS.md) also includes unverified implementations.

| Sampler | Kind | Law and domain | Proof |
| --- | --- | --- | --- |
| `Occil.FactoryExtra.oneDivTwoMinus` | derived | All input biases p in [0,1]; Bernoulli bias 1/(2-p), including both endpoints. | [OneDivTwoMinus](Samplers/OneDivTwoMinus.lean) |
| `Occil.FactoryExtra.reciprocalLogistic` | derived | Every p in [0,1], integer a>=0 and b>0; Bernoulli bias b/(b+a*p), including coefficient zero. | [ReciprocalLogistic](Samplers/ReciprocalLogistic.lean) |
| `Occil.FactoryExtra.integralMixture` | core | Any measurable parameter space, probability measure mu, measurable probability kernel kappa to Bool, and conditionally specified callbacks; target mu.bind kappa. | [IntegralMixture](Samplers/IntegralMixture.lean) |
| `Occil.General.generativeModel` | core | Any probability law on a measurable latent space and any measurable decoder with its deterministic callback contract. | [GenerativeModel](Samplers/GenerativeModel.lean) |
| `Occil.General.inverseQuantile` | core | Every integer scale>1, represented as n+1 with n>0; supplied quantiles on interior ranks1..n. | [InverseQuantile](Samplers/InverseQuantile.lean) |
| `Occil.General.kernelDensity` | core | Every nonempty integer observation list and every normalized integer jitter law, including duplicates and unbounded supports. | [KernelDensity](Samplers/KernelDensity.lean) |
| `Occil.General.uniformBoxPoint` | core | Every positive natural grid scale and every natural dimension, including dimension0. | [UniformBoxPoint](Samplers/UniformBoxPoint.lean) |
| `Occil.flipBits` | core | Every Boolean input list and bias in[0,1], including empty lists and deterministic endpoint coins. | [FlipBits](Samplers/FlipBits.lean) |
| `Occil.DiscreteExtra.betaBinomial` | derived | Every natural trial count and positive rational shapes a/b and c/d, encoded by positive natural a,b,c,d. | [BetaBinomial](Samplers/BetaBinomial.lean) |
| `Occil.Weighted.randomBits` | core | Every natural bit count, including zero; uniform integer law on [0,2^n). | [RandomBits](Samplers/RandomBits.lean) |
| `Occil.DiscreteExtra.symmetricGeometric` | core | All coin biases 0<p<=1, including deterministic p=1; signed integer output with tails proportional to (1-p)^abs(z). | [SymmetricGeometric](Samplers/SymmetricGeometric.lean) |
| `Occil.FactoryExtra.positivePowerSeries` | core | All p in [0,1] and nonnegative integer coefficient lists with positive total, including zero coefficients. | [PositivePowerSeries](Samplers/PositivePowerSeries.lean) |
| `Occil.FactoryExtra.complementPowerSeries` | core | All p in [0,1] and nonnegative coefficient lists of positive total; success is the normalized weighted average of 1-(1-p)^(i+1). | [ComplementPowerSeries](Samplers/ComplementPowerSeries.lean) |
| `Occil.FactoryExtra.complementLogInverse` | derived | Every p in [0,1) including zero; bias (1-p)*log(1/(1-p)). | [ComplementLogInverse](Samplers/ComplementLogInverse.lean) |
| `Occil.FactoryExtra.convexCombination` | core | Nonnegative integer weights with positive total and equally sized callback lists; all component biases in [0,1], including zero-weight categories. | [ConvexCombination](Samplers/ConvexCombination.lean) |
| `Occil.FactoryExtra.oddsProduct` | core | All input and selector biases p,mu in [0,1] with mu<1 or p>0; bias mu*p/(1-mu+mu*p). | [OddsProduct](Samplers/OddsProduct.lean) |
| `Occil.Constants.fromDigits` | core | Every integer base >=2 and any fixed expansion with digits in Fin base, including all-zero and all-maximal expansions. | [FromDigits](Samplers/FromDigits.lean) |
| `Occil.expMinusRational` | core | Every nonnegative integer numerator a and positive integer denominator b; exact Bernoulli exp(-a/b). | [ExpMinusRational](Samplers/ExpMinusRational.lean) |
| `Occil.FactoryExtra.approximateFactory` | core | All input biases, positive natural trial count and scale, and deterministic evaluators specified only on the attainable finite head grid; target is the exact clamped Bernstein mixture. | [ApproximateFactory](Samplers/ApproximateFactory.lean) |
| `Occil.General.stoppedSum` | core | Any normalized natural stopping-count law and normalized integer summand law; no moment assumptions, including zero counts. | [StoppedSum](Samplers/StoppedSum.lean) |
| `Occil.General.episodes` | core | Any normalized natural count law and normalized integer summand law, with the same sampled count retained in the returned pair. | [Episodes](Samplers/Episodes.lean) |
| `Occil.General.kernelDensityVector` | core | Any nonempty list of finite integer vectors and any normalized scalar jitter law; empty or differing vector lengths are permitted. | [KernelDensityVector](Samplers/KernelDensityVector.lean) |
| `Occil.General.stratified1D` | core | Positive strata count at most the positive integer grid scale; bins use exactly floored boundaries. | [Stratified1D](Samplers/Stratified1D.lean) |
| `Occil.General.randomString` | derived | Any natural length over a nonempty alphabet; a separate zero-length spec covers every alphabet, including empty, without a uniform-integer assumption. | [RandomString](Samplers/RandomString.lean) |
| `Occil.General.randomDateTime` | derived | Every nonempty inclusive signed integer timestamp interval, including negative and singleton intervals. | [RandomDateTime](Samplers/RandomDateTime.lean) |
| `Occil.expHalfCoin` | core | No parameters; exact Bernoulli bias exp(-1/2) over mathematical reals. | [ExpHalfCoin](Samplers/ExpHalfCoin.lean) |
| `Occil.gaussianInteger` | core | No parameters; normalized nonnegative integer masses proportional to exp(-k²/2). | [GaussianInteger](Samplers/GaussianInteger.lean) |
| `Occil.FactoryExtra.polylogarithm` | core | Every p in [0,1) including zero, and every positive natural order. | [Polylogarithm](Samplers/Polylogarithm.lean) |
| `Occil.Constants.algebraicRoot` | core | Every p strictly between zero and one, either oracle orientation, and every deterministic sign oracle on the reachable unit-interval rational domain. | [AlgebraicRoot](Samplers/AlgebraicRoot.lean) |
| `Occil.Constants.inverseGoldenRatio` | derived | The concrete parameter-free Bernoulli coin of inverse golden ratio. | [InverseGoldenRatio](Samplers/InverseGoldenRatio.lean) |
| `Occil.FactoryExtra.sigmoidDerivative` | derived | Every signed integer numerator and positive denominator; bias sigmoid(a/b)*(1-sigmoid(a/b)). | [SigmoidDerivative](Samplers/SigmoidDerivative.lean) |
| `Occil.FactoryExtra.sigmoidRational` | derived | Every signed integer numerator and positive integer denominator; bias 1/(1+exp(-a/b)). | [SigmoidRational](Samplers/SigmoidRational.lean) |
| `Occil.FactoryExtra.logisticExp` | derived | Every signed integer z and natural precision including zero; bias 1/(1+exp(z/2^precision)). | [LogisticExp](Samplers/LogisticExp.lean) |
| `Occil.FactoryExtra.exponentialRatio` | derived | Every signed a, positive b, nonnegative x, and positive y; bias (1+exp(a/b-x/y))/(1+exp(a/b)). | [ExponentialRatio](Samplers/ExponentialRatio.lean) |
| `Occil.FactoryExtra.tanhRational` | derived | Every nonnegative integer numerator and positive denominator; exact tanh(a/b). | [TanhRational](Samplers/TanhRational.lean) |
| `Occil.FactoryExtra.reciprocalAffine` | core | Every input bias in [0,1], natural a,b,y positive, and natural x with x*b<=a*y, including x=0. | [ReciprocalAffine](Samplers/ReciprocalAffine.lean) |
| `Occil.FactoryExtra.reciprocalAffinePower` | derived | Every valid reciprocal-affine parameter, input bias, and natural repetition count; a separate zero-count theorem allows arbitrary integer parameters and any callback. | [ReciprocalAffinePower](Samplers/ReciprocalAffinePower.lean) |
| `Occil.FactoryExtra.inverseQuadratic` | derived | Every input bias in [0,1] and every nonnegative integer shift m, including m=0. | [InverseQuadratic](Samplers/InverseQuadratic.lean) |
| `Occil.Constants.sqrtTwoMinusOne` | derived | The concrete parameter-free Bernoulli coin of sqrt(2)-1. | [SqrtTwoMinusOne](Samplers/SqrtTwoMinusOne.lean) |
| `Occil.Constants.inverseSqrtTwo` | derived | The concrete parameter-free Bernoulli coin of 1/sqrt(2). | [InverseSqrtTwo](Samplers/InverseSqrtTwo.lean) |
| `Occil.Constants.goldenFamily` | derived | Positive natural m, ell=1 or ell=-1 with m>=3 in the latter case, and every natural k including zero. | [GoldenFamily](Samplers/GoldenFamily.lean) |
| `Occil.FactoryExtra.offsetRace` | core | All nonnegative rational offsets with positive denominators and positive total exit mass a/b+p+x/y+q; every input bias endpoint is included. | [OffsetRace](Samplers/OffsetRace.lean) |
| `Occil.FactoryExtra.logOverAffine` | derived | All natural a,b with b>0 and b<=a, and every input bias in [0,1], including a=b,p=0. | [LogOverAffine](Samplers/LogOverAffine.lean) |
| `Occil.expMinusFactory` | core | Every input bias p in [0,1], including both endpoints, in the real uniform model. | [ExpMinusFactory](Samplers/ExpMinusFactory.lean) |
| `Occil.FactoryExtra.expTimesComplement` | core | Every input bias p in [0,1], including both deterministic endpoints, in the real uniform model. | [ExpTimesComplement](Samplers/ExpTimesComplement.lean) |
| `Occil.FactoryExtra.reciprocalExpAffine` | derived | All natural a,b,x,y with b>0, b<=a, and y>0, including x=0; exact 1/(a/b+exp(-x/y)). | [ReciprocalExpAffine](Samplers/ReciprocalExpAffine.lean) |
| `Occil.FactoryExtra.expMinusScaled` | core | Every input bias p in [0,1], nonnegative natural numerator x, and positive natural denominator y. | [ExpMinusScaled](Samplers/ExpMinusScaled.lean) |
| `Occil.FactoryExtra.tanhScaled` | derived | Every input bias p in [0,1], natural a including zero, and positive natural b; exact tanh((a/b)*p). | [TanhScaled](Samplers/TanhScaled.lean) |
| `Occil.FactoryExtra.sigmoidScaled` | derived | Every input bias p in [0,1], every signed integer numerator a, and positive natural denominator b; exact sigmoid((a/b)*p). | [SigmoidScaled](Samplers/SigmoidScaled.lean) |
| `Occil.FactoryExtra.exponentialTwist` | core | Every input bias p in [0,1], every signed integer a, and positive integer b; odds multiplied by exp(a/b). | [ExponentialTwist](Samplers/ExponentialTwist.lean) |
| `Occil.FactoryExtra.twoCoin` | core | All nonnegative integer selector weights of positive sum, portkey numerator between zero and its positive denominator, and all input biases with strictly positive weighted accepted mass. | [TwoCoin](Samplers/TwoCoin.lean) |
| `Occil.Weighted.uniformRational` | derived | Every positive natural denominator; integer pair (uniform numerator, fixed denominator). | [UniformFormats](Samplers/UniformFormats.lean) |
| `Occil.Weighted.uniformFixed` | derived | Every positive natural scale; uniform integer output on [0,scale). | [UniformFormats](Samplers/UniformFormats.lean) |
| `Occil.Weighted.uniformDyadic` | derived | Every natural bit count, including zero; pair (uniform numerator, 2^bits). | [UniformFormats](Samplers/UniformFormats.lean) |
| `Occil.DiscreteExtra.negativeHypergeometric` | core | Natural r, ones, zeros with r<=ones; includes zero requests, empty urn, and exhausted unmarked color. | [NegativeHypergeometric](Samplers/NegativeHypergeometric.lean) |
| `Occil.DiscreteExtra.himanshu` | derived | Positive natural block size and coin bias 0<p<=1; failed independent blocks before the first all-success block. | [Himanshu](Samplers/Himanshu.lean) |
| `Occil.Weighted.moduloReduction` | core | Every positive natural target width and every natural bit count, including zero; target width may exceed word width. | [WordReductions](Samplers/WordReductions.lean) |
| `Occil.Weighted.multiplyShift` | core | Every positive natural target width and every natural bit count, including zero; target width may exceed word width. | [WordReductions](Samplers/WordReductions.lean) |
| `Occil.WeightedVariants.sequentialCoins` | core | All natural lists of weights with positive total, including leading, interior and trailing zeros. | [SequentialCoins](Samplers/SequentialCoins.lean) |
| `Occil.DiscreteExtra.binomialHalfBits` | core | Every natural number of fair trials, including zero. | [BinomialHalfBits](Samplers/BinomialHalfBits.lean) |
| `Occil.poissonOne` | core | The parameter-free integer-only Poisson sampler, with canonical Poisson(1) target. | [PoissonOne](Samplers/PoissonOne.lean) |
| `Occil.poissonRational` | core | All natural numerators x and positive natural denominators y, including zero, integer and fractional rates. | [PoissonRational](Samplers/PoissonRational.lean) |
| `Occil.Weighted.bitmaskRejection` | core | Every positive natural target width, including one. | [BitmaskRejection](Samplers/BitmaskRejection.lean) |
| `Occil.DiscreteExtra.compoundPoisson` | core | Every nonnegative rational rate and arbitrary countable latent probability measure with an integer-valued jump map, including fully signed integer jumps. | [CompoundPoisson](Samplers/CompoundPoisson.lean) |
| `Occil.DiscreteExtra.skellam` | core | Two arbitrary nonnegative rational rates; both natural denominators positive, either or both numerators may vanish. | [Skellam](Samplers/Skellam.lean) |
| `Occil.DiscreteExtra.neymanTypeA` | derived | Arbitrary nonnegative rational Poisson count and cluster rates, each denominator positive. | [NeymanTypeA](Samplers/NeymanTypeA.lean) |
| `Occil.DiscreteExtra.polyaAeppli` | derived | Arbitrary nonnegative rational Poisson rate; positive rational geometric success probability a/b with a<=b, including probability one. | [PolyaAeppli](Samplers/PolyaAeppli.lean) |
| `Occil.DiscreteExtra.zeroTruncatedPoisson` | core | Every strictly positive rational rate x/y with natural positive numerator and denominator. | [ZeroTruncatedPoisson](Samplers/ZeroTruncatedPoisson.lean) |
| `Occil.DiscreteExtra.multivariatePoisson` | core | Every nonnegative rational shared rate and every finite list of nonnegative rational residual rates, with positive denominators; includes an empty component list. | [MultivariatePoisson](Samplers/MultivariatePoisson.lean) |
| `Occil.DiscreteExtra.logUniform` | core | Every nonnegative inclusive maximum and natural base at least two, including maximum zero. | [LogUniform](Samplers/LogUniform.lean) |
| `Occil.gaussian` | core | Exact standard Gaussian over mathematical reals, with the actual integer-bit fair sign primitive. | [Gaussian](Samplers/Gaussian.lean) |
| `Occil.orderStatistic` | core | Every rank1≤k≤n, using a normalized iid uniform real vector and the canonical kth-sorted-value encoder; ties retain multiplicity. | [OrderStatistic](Samplers/OrderStatistic.lean) |
| `Occil.General.bootstrap` | derived | Every finite empirical data set and natural replicate count; an empty-data spec needs no uniform-integer class. | [Bootstrap](Samplers/Bootstrap.lean) |
| `Occil.General.histogram` | core | Nonnegative integer bin counts of positive total, one more boundary than counts, and strictly positive integer bin widths; zero counts are permitted. | [Histogram](Samplers/Histogram.lean) |
| `Occil.shuffle` | core | Every finite list, including empty lists and duplicate values, with arbitrary value encoders. | [Shuffle](Samplers/Shuffle.lean) |
| `Occil.positiveComposition` | core | Every positive part count n and total≥n. | [PositiveComposition](Samplers/PositiveComposition.lean) |
| `Occil.weakComposition` | derived | Every positive part count n and every natural total, including zero. | [WeakComposition](Samplers/WeakComposition.lean) |
| `Occil.General.latinHypercube1D` | core | Every integer grid with 1≤strata≤scale. | [LatinHypercube1D](Samplers/LatinHypercube1D.lean) |
| `Occil.General.stratifiedBox` | core | Positive grid dimension,1≤bins≤scale, and every natural per-cell draw count including zero. | [StratifiedBox](Samplers/StratifiedBox.lean) |
| `Occil.General.classifiedModel` | core | Nonnegative integer class weights of positive sum and a matching finite family of normalized specified class-conditional callbacks; zero class weights are allowed. | [ClassifiedModel](Samplers/ClassifiedModel.lean) |
| `Occil.General.markovChain` | core | Every square nonnegative integer-weight transition matrix with positive row totals, valid initial state and finite natural step count; the separate zero-step spec accepts arbitrary matrix and initial values without uniform randomness. | [MarkovChain](Samplers/MarkovChain.lean) |
| `Occil.General.randomMap` | core | Every finite list of positive-total nonnegative integer rows, including no rows; row lengths need not be equal. | [RandomMap](Samplers/RandomMap.lean) |
| `Occil.General.randomWalkPath` | core | Every normalized integer increment callback, signed integer start and natural step count. | [RandomWalkPath](Samplers/RandomWalkPath.lean) |
| `Occil.sattolo` | core | Every finite list and arbitrary value encoder, including empty, singleton and duplicate-valued lists. | [Sattolo](Samplers/Sattolo.lean) |
| `Occil.General.permutationSamples` | derived | Every finite observation list and natural replicate count, including empty observations, duplicate values and zero replicates. | [PermutationSamples](Samplers/PermutationSamples.lean) |
| `Occil.General.stoppedMinimum` | core | Every normalized integer observation callback and independent almost-surely positive natural count callback; no count bound or moment assumption. | [StoppedMinimum](Samplers/StoppedMinimum.lean) |
| `Occil.General.stoppedMaximum` | core | Every normalized integer observation callback and independent almost-surely positive natural count callback; no count bound or moment assumption. | [StoppedMaximum](Samplers/StoppedMaximum.lean) |
| `Occil.General.markovTrajectory` | core | Every square positive-total-row nonnegative integer matrix, valid initial state and natural step count; zero steps also support arbitrary matrix/initial values without a uniform-integer primitive. | [MarkovTrajectory](Samplers/MarkovTrajectory.lean) |
| `Occil.General.gibbsSweep` | core | Every natural sweep dimension, countable measurably encoded state space and normalized supplied coordinate kernels; callback contracts are required only for indices below dimension. | [GibbsSweep](Samplers/GibbsSweep.lean) |
| `Occil.General.randomScanGibbs` | core | Positive coordinate count, countable measurable encoded states, supplied normalized coordinate callbacks and all natural update counts; a separate zero-update theorem accepts arbitrary callback/initial values without uniform randomness. | [RandomScanGibbs](Samplers/RandomScanGibbs.lean) |
| `Occil.randomGraph` | core | Every natural vertex count and Bernoulli callback bias p∈[0,1], including empty/singleton graphs and both deterministic bias endpoints; no random primitive assumption beyond the supplied callback contract. | [RandomGraph](Samplers/RandomGraph.lean) |
| `Occil.reservoir` | core | Every finite list with arbitrary encoder and natural capacity0≤k≤length, including duplicate values, zero capacity, empty input and full capacity. | [Reservoir](Samplers/Reservoir.lean) |
| `Occil.Weighted.weightedReservoirOne` | core | Every natural weight list with positive total, including leading, interior and trailing zeros. | [WeightedReservoirOne](Samplers/WeightedReservoirOne.lean) |
| `Occil.WeightedVariants.divisionRejection` | core | Every positive natural target n and natural bit count with n<=2^bits; includes n=1,bits=0 and exact power-of-two ranges. | [DivisionRejection](Samplers/DivisionRejection.lean) |
| `Occil.WeightedVariants.debiasedModulo` | core | Every positive natural target n and natural bit count with n<=2^bits; includes n=1,bits=0 and exact power-of-two ranges. | [DebiasedModulo](Samplers/DebiasedModulo.lean) |
| `Occil.FactoryExtra.expMinusPolynomial` | core | Every input bias p in [0,1] and every finite list of nonnegative rational coefficients with positive denominators, including zero coefficients and the empty list. | [ExpMinusPolynomial](Samplers/ExpMinusPolynomial.lean) |
| `Occil.DiscreteExtra.binomialBinary` | core | All natural trial counts and rational bias a/b with b>0,a<=b; includes zero trials and both bias endpoints. | [BinomialBinary](Samplers/BinomialBinary.lean) |
| `Occil.DiscreteExtra.cub` | derived | All natural m>=3 and rational selector/uncertainty biases a/b,c/d in [0,1], with positive denominators. | [Cub](Samplers/Cub.lean) |
| `Occil.WeightedVariants.flatChoice` | core | Every natural weight list with positive total, including zeros in every position and no table-size bound. | [FlatChoice](Samplers/FlatChoice.lean) |
| `Occil.WeightedVariants.lemireUniform` | core | Every positive natural target n fitting in 2^bits, with arbitrary natural bits including the zero-bit singleton endpoint. | [LemireUniform](Samplers/LemireUniform.lean) |
| `Occil.General.permutationTest` | core | Every finite observation list, arbitrary valid deterministic integer statistic and natural replicate count, including empty input, duplicates and zero trials. | [PermutationTest](Samplers/PermutationTest.lean) |
| `Occil.General.groupedPermutation` | derived | Arbitrary observation types/encoders and nonnegative group sizes summing to the observation count; zero sizes, empty observations and duplicate values are included. | [GroupedPermutation](Samplers/GroupedPermutation.lean) |
| `Occil.General.pdfRejection` | core | Every signed nonempty half-open integer proposal interval, positive integer envelope, natural height bounded on that interval, and positive total acceptance mass. The pure density callback is specified only on proposal points. | [PdfRejection](Samplers/PdfRejection.lean) |
| `Occil.General.latinHypercube` | derived | Every integer grid with1≤count≤scale and every positive dimension. | [LatinHypercube](Samplers/LatinHypercube.lean) |
| `Occil.General.inverseCDF` | core | Positive integer CDF denominator, signed nonempty closed integer grid, nondecreasing CDF in[0,scale] with cdf(upper)=scale; singleton grids, plateaus and nonzero lower atoms are included. Oracle contracts are required only on the grid. | [InverseCDF](Samplers/InverseCDF.lean) |
| `Occil.FactoryExtra.gambler` | core | All input biases, natural heights, and positive integer a,b; separate base theorem covers every integer height<=1 with arbitrary rational parameters and callback, without a uniform-integer assumption. | [Gambler](Samplers/Gambler.lean) |
| `Occil.FactoryExtra.highPowerLogistic` | derived | All input biases, natural heights, positive integer a,b; separate base theorem covers every integer height<=0 and arbitrary parameters/callback without a uniform-integer assumption. | [HighPowerLogistic](Samplers/HighPowerLogistic.lean) |
| `Occil.Constants.generalizedContinuedFraction` | core | All positive integer numerators bounded by their denominators, every terminal-flag sequence and natural start, with a deterministic coefficient oracle required only at positions reachable before the first terminal flag. | [GeneralizedContinuedFraction](Samplers/GeneralizedContinuedFraction.lean) |
| `Occil.Constants.continuedFraction` | derived | Every positive simple denominator sequence with arbitrary terminal flags and a deterministic oracle only on reachable indices beginning at one. | [ContinuedFraction](Samplers/ContinuedFraction.lean) |
| `Occil.DiscreteExtra.borel` | core | All natural numerators x<y, equivalently rational rates0<=x/y<1; includes zero rate. The actual guard excludes the critical endpoint. | [Borel](Samplers/Borel.lean) |
| `Occil.WeightedVariants.oneillUniform` | core | Every positive natural target n fitting in2^bits; all natural bits, including zero-bit n=1 and n=source-width endpoints. | [OneillUniform](Samplers/OneillUniform.lean) |
| `Occil.DiscreteExtra.fisherHypergeometric` | core | All natural draws n<=ones+zeros and positive natural odds numerator/denominator a,b; includes empty draw, either empty color and complete population. | [FisherHypergeometric](Samplers/FisherHypergeometric.lean) |
| `Occil.FactoryExtra.linear` | core | All unit-interval biases, integer a>=0,b>0; only the expanding branch requires 0<e<f and (a/b)*p<=1-e/f. Contracting coefficients admit arbitrary integer margins. | [LinearFactory](Samplers/LinearFactory.lean) |
| `Occil.Constants.fromBounds` | core | Every unit-interval target, deterministic rational enclosures from index zero, and arbitrarily small widths; no monotonicity or convergence rate is assumed. | [FromBounds](Samplers/FromBounds.lean) |
| `Occil.logOnePlusFactory` | core | Every unit-interval input bias including zero and one, with an arbitrary verified callback and arbitrary ENNReal credits. | [LogOnePlusFactory](Samplers/LogOnePlusFactory.lean) |
| `Occil.FactoryExtra.complementLogOnePlus` | derived | Every unit-interval input bias and arbitrary verified callback, including both endpoints and arbitrary ENNReal credits. | [ComplementLogOnePlus](Samplers/ComplementLogOnePlus.lean) |
| `Occil.DiscreteExtra.logarithmicSeries` | core | All natural rational parameters0<a<b, exactly the actual strict guard domain. | [LogarithmicSeries](Samplers/LogarithmicSeries.lean) |
| `Occil.multinomial` | core | All natural trial counts and natural category-weight lists with n=0 or positive total weight; includes empty/all-zero lists at zero trials and zero weights in any position. | [Multinomial](Samplers/Multinomial.lean) |
| `Occil.weightedWithoutReplacement` | core | Every natural weight list and natural request k bounded by its number of positive weights; k=0 permits empty and all-zero lists. | [WeightedWithoutReplacement](Samplers/WeightedWithoutReplacement.lean) |
| `Occil.Weighted.cumulativeDraw` | core | Every nonempty finite monotone bounded integer cumulative array on indices0..n-1, with positive stored total equal to its terminal cumulative value; includes plateaus and positive initial cumulative mass. | [CumulativeDraw](Samplers/CumulativeDraw.lean) |
| `Occil.Weighted.cumulativeChoice` | derived | Every natural weight list of positive total, including leading/interior/trailing zeros and arbitrary positive singleton weights. | [CumulativeChoice](Samplers/CumulativeChoice.lean) |
| `Occil.FactoryExtra.linearPower` | derived | All unit-interval biases, natural powers and the complete conditional-margin Linear domain. An additional zero-power theorem covers arbitrary integer parameters and unknown callbacks without UniformInt. | [LinearPower](Samplers/LinearPower.lean) |
| `Occil.FactoryExtra.addition` | derived | All unit-interval component biases with a supplied rational margin 0<e<f and p+q<=1-e/f, including zero components and equality at the margin. | [Addition](Samplers/Addition.lean) |
| `Occil.FactoryExtra.subtraction` | derived | All unit-interval component biases and rational margins 0<e<f with e/f<=p-q, including a zero subtrahend and equality at the margin. | [Subtraction](Samplers/Subtraction.lean) |
| `Occil.FactoryExtra.division` | derived | All unit-interval denominator p and numerator q with 0<e<f and e/f<=p-q, including q=0. | [Division](Samplers/Division.lean) |
| `Occil.FactoryExtra.affine` | derived | All integer a,b,y>0,x>=0; only an expanding final coefficient (x+y)*b>y*a requires 0<e<f and (x/y+p)/(a/b)<=1-e/f. Contracting cases retain arbitrary integer margins. | [AffineFactory](Samplers/AffineFactory.lean) |
| `Occil.FactoryExtra.affineRatio` | core | All natural offsets a,x>=0 and positive denominators b,y; either x*b+b*y<=a*y with arbitrary integer margins, or 0<e<f and e/f bounded by the literal normalized denominator-minus-numerator gap. | [AffineRatio](Samplers/AffineRatio.lean) |
| `Occil.uniformFromModulus` | core | Every natural source modulus at least two and every positive natural target, with no target/source-size restriction. | [UniformFromModulus](Samplers/UniformFromModulus.lean) |
| `Occil.DiscreteExtra.negativeMultinomial` | core | Every natural requested success count, positive natural success weight and arbitrary natural failure-weight list; includes zero requests, empty lists, all-zero failures and zero weights in any position. | [NegativeMultinomial](Samplers/NegativeMultinomial.lean) |
| `Occil.DiscreteExtra.walleniusHypergeometric` | core | Every feasible natural draw count n≤ones+zeros and strictly positive natural odds a,b, including zero draws, empty colors and complete depletion. | [WalleniusHypergeometric](Samplers/WalleniusHypergeometric.lean) |
| `Occil.derangement` | core | Every natural size other than one, including zero. | [Derangement](Samplers/Derangement.lean) |
| `Occil.General.metropolisHastings` | core | Every countable encoded state space, normalized proposal measures whose singleton probabilities are represented by natural numerators and positive natural denominators, natural target weights and a positive-weight initial state, all natural transition counts. Unrestricted zero transitions require no callback contracts or random primitive. | [CountableMetropolisHastings](Samplers/CountableMetropolisHastings.lean) |
| `Occil.General.metropolis` | derived | Every countable encoded state space, arbitrary normalized proposal measures, natural target weights and a positive-weight initial state, all natural transition counts. Symmetry is not required for the execution law; a stationary probability-target interpretation additionally needs symmetry and normalizability. Unrestricted zero transitions require no callback contracts or random primitive. | [CountableMetropolis](Samplers/CountableMetropolis.lean) |
| `Occil.General.discreteCDF` | core | Every nonnegative nondecreasing finite cumulative table with positive final mass, including leading zeros, plateaus, singleton tables and a nonzero lower atom. | [DiscreteCDF](Samplers/DiscreteCDF.lean) |
| `Occil.General.piecewiseConstant` | core | Every strict signed integer partition with matching nonnegative natural bin heights and positive total grid mass; zero-height bins are included. | [PiecewiseConstant](Samplers/PiecewiseConstant.lean) |
| `Occil.General.piecewiseLinear` | core | Every strict signed integer vertex grid with nonnegative natural heights and positive total half-open interpolated grid mass, including zero vertices and zero-profile bins. | [PiecewiseLinear](Samplers/PiecewiseLinear.lean) |
| `Occil.FactoryExtra.epsilonDivision` | derived | All unit-interval p, integers 0<=a<b, positive lower denominator and lower numerator<=denominator; positive a additionally requires certified lower> a/b and p>=lower. Separate zero and unit-lower theorems require no input callback contract; zero also requires no UniformInt and permits negative lower numerators. | [EpsilonDivision](Samplers/EpsilonDivision.lean) |
| `Occil.factorialSeriesFactory` | core | All unit-interval input biases including0/1, each actual mode0/1/2 and arbitrary verified input callbacks; arbitrary masks and ENNReal credits. | [FactorialSeriesFactory](Samplers/FactorialSeriesFactory.lean) |
| `Occil.expMinusMartingale` | derived | Every unit-interval input bias, arbitrary verified callback and arbitrary ENNReal output credits, including both endpoints. | [ExpMinusMartingale](Samplers/ExpMinusMartingale.lean) |
| `Occil.cosineFactory` | derived | Every unit-interval input bias, arbitrary verified callback and arbitrary ENNReal output credits, including both endpoints. | [CosineFactory](Samplers/CosineFactory.lean) |
| `Occil.sineFactory` | derived | Every unit-interval input bias includingzero/one, arbitrary verified callback and arbitrary ENNReal output credits. | [SineFactory](Samplers/SineFactory.lean) |
| `Occil.Weighted.rationalChoice` | derived | All raw natural numerator/denominator pairs with strictly positive denominators and positive numerator sum; no coprimality, reduction or size assumptions. | [RationalChoice](Samplers/RationalChoice.lean) |
| `Occil.Weighted.uniformBinaryFloat` | core | All natural precisions and leading-zero caps, including both zero endpoints. | [UniformBinaryFloat](Samplers/UniformBinaryFloat.lean) |
| `Occil.General.couplingFromPast` | core | Every normalized iid map law on a nonempty finite state space, a stationary probability law, and positive probability of coalescence in some finite iid word. No single-map or strictly-positive-matrix hypothesis is imposed. | [CouplingFromPast](Samplers/CouplingFromPast.lean) |
| `Occil.General.perfectFiniteChain` | derived | Every nonempty square matrix of natural transition weights with positive row totals, stationary probability law, and positive coalescence probability for a finite word of its actual independently sampled shared-map law; zero matrix entries are allowed. | [PerfectFiniteChain](Samplers/PerfectFiniteChain.lean) |
| `Occil.General.sliceSampler` | core | Every positive-width signed integer proposal grid with natural density weights, positive grid starting state and natural transition count. Additional public specs cover arbitrary outside-grid starting values with positive cap bounded by a grid anchor, and unrestricted zero steps with arbitrary values and no random-primitive assumption. | [SliceSampler](Samplers/SliceSampler.lean) |
| `Occil.DiscreteExtra.walleniusMultivariate` | core | Natural population counts and request at most their sum, matching positive integer odds, including empty urn with zero request and zero-population classes. | [WalleniusMultivariate](Samplers/WalleniusMultivariate.lean) |
| `Occil.DiscreteExtra.multivariateHypergeometric` | derived | Every natural finite multicolor population and natural request at most its sum, including empty input, zero-population colors and zero draws. | [MultivariateHypergeometric](Samplers/MultivariateHypergeometric.lean) |
| `Occil.WeightedVariants.voseSamples` | core | Every finite list of nonnegative natural weights with positive total and every natural sample count, including zero counts and zero-weight categories. | [VoseSamples](Samplers/VoseSamples.lean) |
| `Occil.FactoryExtra.expMinusShifted` | derived | Every unit-interval input bias and all integer shifts a>=0,b>0, including zero shift and both input endpoints, with arbitrary verified callbacks. | [ExpMinusShifted](Samplers/ExpMinusShifted.lean) |
| `Occil.FactoryExtra.tanhHalfShifted` | derived | Every unit-interval input bias and integer a>=0,b>0, including zero shift and both endpoints. | [TanhHalfShifted](Samplers/TanhHalfShifted.lean) |
| `Occil.FactoryExtra.expMinusShiftPower` | core | Every unit-interval input bias and all natural m,k including zero, with arbitrary verified callbacks and ENNReal output credits. | [ExpMinusShiftPower](Samplers/ExpMinusShiftPower.lean) |
| `Occil.Constants.fromApproximateDigits` | core | All natural bases>=2, unit-interval probabilities and integer approximations at source positions n+1 with absolute integer error<=1. The deterministic callback is required only on those positive source positions; arbitrary callback free variables are retained. | [FromApproximateDigits](Samplers/FromApproximateDigits.lean) |
| `Occil.DiscreteExtra.fisherMultivariate` | core | All natural capacities and strictly positive natural odds lists of equal length, and every requested draw count bounded by total capacity; includes empty, zero-capacity, zero-draw and full-population cases. | [FisherMultivariate](Samplers/FisherMultivariate.lean) |
| `Occil.WeightedVariants.twoLevelChoice` | core | Every positive natural block size and nonnegative natural weight list of positive total; includes all-zero blocks, partial last blocks, singleton blocks and sizes larger than the list. | [TwoLevelChoice](Samplers/TwoLevelChoice.lean) |
| `Occil.Weighted.fyky` | core | Every positive natural exclusive bound, with a separate deterministic singleton specification requiring no UniformInt primitive. | [FYKY](Samplers/FYKY.lean) |
| `Occil.DiscreteExtra.discreteLaplace` | core | Every strictly positive natural rate numerator s and denominator t, including s/t below and above one. | [DiscreteLaplace](Samplers/DiscreteLaplace.lean) |
| `Occil.WeightedVariants.floatingMultiply` | core | All positive natural n≤2^bits with natural bits≤precision and strictly positive precision. The outer-valid corner n1/bits0/precision0 invokes an invalid rounding format and has no normalized sampler claim. | [FloatingMultiply](Samplers/FloatingMultiply.lean) |
| `Occil.fastDiceRoller` | core | Every positive natural exclusive bound, including a separate deterministic singleton specification requiring no UniformInt primitive. | [FastDiceRoller](Samplers/FastDiceRoller.lean) |
| `Occil.WeightedVariants.fenwickDraw` | core | Every finite natural weight vector of positive total and every caller-owned exact Fenwick representation, including zero weights and non-power-of-two lengths. Supporting constructor accepts every positive-total natural list; supporting setter accepts every valid position and natural replacement, including a zero-total result. Bare ownership permits total zero, while drawing requires positive total. | [FenwickDraw](Samplers/FenwickDraw.lean) |
| `Occil.Constants.eScaled` | derived | All natural numerator u>=0 and denominator v>0 satisfying the exact probability condition exp(1)*u/v<=1. No v>=3u or early-enclosure upper<=1 restriction. | [EScaled](Samplers/EScaled.lean) |
| `Occil.Constants.eOverPi` | derived | The fixed canonical probability exp(1)/pi, arbitrary masks, ghost states, measurable Boolean credits including infinity, and arbitrary resource frames. | [EOverPi](Samplers/EOverPi.lean) |
| `Occil.Constants.piAffine` | derived | Every signed integer offset, positive natural divisor, and exact0<=pi-offset<=divisor probability domain. Negative offsets remain admissible. | [PiAffine](Samplers/PiAffine.lean) |
| `Occil.Constants.reciprocalPiScaled` | derived | Every natural numerator including zero, positive natural denominator, and exact numerator<=denominator*pi bound. Coarse interval endpoints may exceed1. | [ReciprocalPiScaled](Samplers/ReciprocalPiScaled.lean) |
| `Occil.Constants.inverseEPlusRational` | derived | All natural a>=b>0, including a=b and nonreduced rational parameters; arbitrary masks, ghost states and ENNReal credits. | [InverseEPlusRational](Samplers/InverseEPlusRational.lean) |
| `Occil.Constants.exponentialRationalProduct` | derived | All natural x,z>=0 and y,t>0 with the sole exact probability restriction exp(-x/y)*z/t<=1. Compensated z>t and arbitrary x/y>1 are included. | [ExponentialRationalProduct](Samplers/ExponentialRationalProduct.lean) |
| `Occil.Constants.fromPositiveSeries` | core | Every summable nonnegative rational coefficient stream with positive term/error denominators, total sum<=1 and certified arbitrarily small nonnegative tail bounds. No monotonicity/rate, positive coefficients, strict mass bound or callback-FV restriction. | [FromPositiveSeries](Samplers/FromPositiveSeries.lean) |
| `Occil.Constants.threeZetaThreeOverFour` | derived | The fixed normalized probability3/4 times the ordinary convergent reciprocal-cube series zeta(3), arbitrary masks, ghost states, Boolean credits including infinity and resource frames. | [ThreeZetaThreeOverFour](Samplers/ThreeZetaThreeOverFour.lean) |
| `Occil.aliasSamples` | core | Every finite list of nonnegative natural weights with positive total and every natural sample count, including zero repetitions and zero-weight categories. | [AliasSamples](Samplers/AliasSamples.lean) |

<!-- expansion:end -->

## Reading and checking the proofs

Read the target law and credit kernel, the central expectation lemma, then the
`twp_*` theorem. Retrying algorithms isolate the amplification facts needed for
total correctness. `SampleWithReplacement` includes a separate zero-draw public
spec covering empty input without any uniform-randomness assumption.

Independent review findings, suggestions, source snapshots, and reproducible
caller/boundary/infinite-credit checks are under
[`agent-docs/reviews`](../agent-docs/reviews). The complete audit is reproducible:

```sh
python3 agent-scripts/audit_sampler_proofs.py --check-callers
```

This runs the full project build, binds accepted proofs to reviewer-owned receipts
and transitive source/dependency snapshots, inspects actual compiled spec program
heads, audits transitive axioms, and compiles the independent caller checks.
Add `--require-complete` to enforce the expansion campaign's completion target.
Mathematical interpretation and domain adequacy are established by human-style
source review; the script's structural sanity checks do not decide those claims.

These are ideal ProbLang correctness proofs. Float interpreter statistics remain
separate implementation evidence.
