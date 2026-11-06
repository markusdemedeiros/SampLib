# Native-real implementation queue

This plan dates from 6 November 2026 and targets `clutch-lean` commit `06a7b3e2`. It plans
implementation and verification. The counts in the estimates section are estimates, not
new proofs or claims of completeness. The plan uses no foreign function interface (FFI)
and adds no new fixed-point or grid approximation work.

For exact work, which excludes all grid and numerical work, use the
[exact verification queue](ExactVerificationQueue.md) of **137 entries**. Round 2 closed on
6 November 2026 with 120 entries accepted and 17 deferred; see the
[deferred samplers](ExactCampaignDeferrals.md). That queue does not include the native-real
port estimates in this plan.

## Estimates

The plan rests on these estimates:

- **Bernoulli backlog from `LAWS.md`: 68 entries**, all with code: **33 ordinary
  factories, 3 lazy-coin samplers, and 32 constant coins**. `LAWS.md` now marks all 63
  exact entries verified. Only the five numerical constant coins lack a proof, and their
  native-real replacements belong in the port queue.
- **Additional Bernoulli implementations:** Expect roughly **6 to 10 shared construction entry
  points**, plus named specializations after an audit of each source. This number estimates
  the engine, not the size of the Bernoulli proof backlog. It does
  not establish that the sources are complete.
- **Native-real ports:** Expect roughly **170 to 200 useful sampler entry points**, drawn
  from the 224 numerical catalog entries in the candidate inventory. These include
  native-real versions of existing techniques, not 170 to 200 algorithms that were absent
  before. Exclude arithmetic helpers, central limit theorem (CLT) approximations,
  duplicate wrappers, and constructions that still need exact cumulative distribution
  functions (CDFs) that are not available.
- Track these three queues separately: proofs of current terms, additional factory
  algorithms, and native-real ports. Do not add proof counts to implementation counts. The
  estimates concern scope. Give no estimate of elapsed time until representative
  implementations and proofs exist.

## Bernoulli proof backlog (68)

This table lists each entry of the backlog with its proof status in [LAWS.md](../LAWS.md),
including the constant and lazy coins. Every row already has implementation code. A dash
in the proof column of `LAWS.md` means that the index has no accepted stand-alone proof,
not that the implementation is missing. New real primitives do not automatically prove the
existing series, lazy-state, or permutation constructions. Verify their actual terms. Do
not substitute a direct known-probability coin and call it the same proof.

| Entry | Intended law | Code | Proof |
| --- | --- | --- | --- |
| `Occil.fractionalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Basic.lean](../code/Samplers/Bernoulli/Basic.lean#L51) | [Verified](../SampLib/Bernoulli/FractionalPower.lean) |
| `Occil.FactoryExtra.complementOverLogInverse` | $\mathrm{Bern}\!\left(\frac{1-p}{\log(1/p)}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L107) | [Verified](../SampLib/Bernoulli/LogRatioFactories.lean) |
| `Occil.FactoryExtra.expIntegral` | $\mathrm{Bern}\!\left(\frac{1-e^{-(m+p)}}{m+p}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L71) | [Verified](../SampLib/Bernoulli/ExpIntegral.lean) |
| `Occil.FactoryExtra.pOverLogInverseComplement` | $\mathrm{Bern}\!\left(\frac p{\log(1/(1-p))}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L101) | [Verified](../SampLib/Bernoulli/LogRatioFactories.lean) |
| `Occil.FactoryExtra.binaryExponential` | $\mathrm{Bern}\!\left(2^{-m(k+p)}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L88) | [Verified](../SampLib/Bernoulli/BinaryExponential.lean) |
| `Occil.FactoryExtra.binaryExponentialRational` | $\mathrm{Bern}\!\left(2^{-ap/b}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L98) | [Verified](../SampLib/Bernoulli/BinaryExponentialRational.lean) |
| `Occil.FactoryExtra.expDivThree` | $\mathrm{Bern}\!\left(e^p/3\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L65) | [Verified](../SampLib/Bernoulli/ExpDivThree.lean) |
| `Occil.FactoryExtra.expMinusExp` | $\mathrm{Bern}\!\left(e^{-e^{m+p}}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L72) | [Verified](../SampLib/Bernoulli/ExpMinusExp.lean) |
| `Occil.FactoryExtra.expSquareTimesComplement` | $\mathrm{Bern}\!\left(e^{p^2}(1-p)\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L82) | [Verified](../SampLib/Bernoulli/ExpSquareTimesComplement.lean) |
| `Occil.FactoryExtra.linear2014` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L129) | [Verified](../SampLib/Bernoulli/Linear2014.lean) |
| `Occil.FactoryExtra.linearLowProbability` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L93) | [Verified](../SampLib/Bernoulli/LinearLowProbability.lean) |
| `Occil.FactoryExtra.linearPowerWalk` | $\mathrm{Bern}\!\left((cp)^m\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L108) | [Verified](../SampLib/Bernoulli/LinearPowerWalk.lean) |
| `Occil.FactoryExtra.polynomial` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L19) | [Verified](../SampLib/Bernoulli/PolynomialFactory.lean) |
| `Occil.FactoryExtra.rationalFunction` | $\mathrm{Bern}\!\left(f(p)/g(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L48) | [Verified](../SampLib/Bernoulli/RationalFunction.lean) |
| `Occil.FactoryExtra.threePointPiecewise` | $\mathrm{Bern}(f(p)),\ f\text{ piecewise affine}$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L57) | [Verified](../SampLib/Bernoulli/ThreePointPiecewise.lean) |
| `Occil.FactoryExtra.rationalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L15) | [Verified](../SampLib/Common/RationalPower.lean) |
| `Occil.FactoryExtra.twoCoinPower` | $\mathrm{Bern}\!\left(p^q\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L24) | [Verified](../SampLib/Bernoulli/TwoCoinPower.lean) |
| `Occil.FactoryExtra.alternatingSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}(-1)^nc_np^n\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L20) | [Verified](../SampLib/Bernoulli/AlternatingSeries.lean) |
| `Occil.FactoryExtra.envelopeFactory` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L118) | [Verified](../SampLib/Bernoulli/EnvelopeFactory.lean) |
| `Occil.FactoryExtra.envelopeFactoryDegrees` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L79) | [Verified](../SampLib/Bernoulli/EnvelopeFactory.lean) |
| `Occil.FactoryExtra.minimumComplement` | $\mathrm{Bern}\!\left(\min(p,1-p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L135) | [Verified](../SampLib/Bernoulli/MinimumComplement.lean) |
| `Occil.FactoryExtra.minimumHalf` | $\mathrm{Bern}(\min(p,1/2))$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L150) | [Verified](../SampLib/Bernoulli/MinimumHalf.lean) |
| `Occil.FactoryExtra.powerSeriesHazards` | $\mathrm{Bern}\!\left(1-\sum_{n\ge0}c_n(1-p)^{n+1}\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L50) | [Verified](../SampLib/Bernoulli/PowerSeriesHazards.lean) |
| `Occil.FactoryExtra.alternatingPermutation` | $\mathrm{Bern}\!\left(\begin{cases}(1-p)/\cos p&r=0\\(1-p)\tan p&r=1\end{cases}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L47) | [Verified](../SampLib/Bernoulli/AlternatingPermutation.lean) |
| `Occil.FactoryExtra.arcsineHalf` | $\mathrm{Bern}\!\left(\frac12\arcsin p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L81) | [Verified](../SampLib/Bernoulli/ArcsineFactories.lean) |
| `Occil.FactoryExtra.arcsinePlusSqrtMinusOne` | $\mathrm{Bern}\!\left(\arcsin p+\sqrt{1-p^2}-1\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L69) | [Verified](../SampLib/Bernoulli/ArcsineFactories.lean) |
| `Occil.FactoryExtra.arctanOverPi` | $\mathrm{Bern}\!\left(\arctan(p)/\pi\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L32) | [Verified](../SampLib/Bernoulli/ArctanOverPi.lean) |
| `Occil.FactoryExtra.complementOverCosine` | $\mathrm{Bern}\!\left(\frac{1-p}{\cos p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L61) | [Verified](../SampLib/Bernoulli/AlternatingPermutation.lean) |
| `Occil.FactoryExtra.complementTimesTangent` | $\mathrm{Bern}\!\left((1-p)\tan p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L64) | [Verified](../SampLib/Bernoulli/AlternatingPermutation.lean) |
| `Occil.FactoryExtra.cosineSqrt` | $\mathrm{Bern}\!\left(\cos\sqrt p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L26) | [Verified](../SampLib/Bernoulli/TrigonometricSeriesFactories.lean) |
| `Occil.FactoryExtra.pOverTangent` | $\mathrm{Bern}\!\left(\frac p{\tan p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L88) | [Verified](../SampLib/Bernoulli/POverTangent.lean) |
| `Occil.FactoryExtra.sincScaled` | $\mathrm{Bern}\!\left(\frac{\sin(p\sqrt c)}{p\sqrt c}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L17) | [Verified](../SampLib/Bernoulli/TrigonometricSeriesFactories.lean) |
| `Occil.FactoryExtra.sincSqrtScaled` | $\mathrm{Bern}\!\left(\frac{\sin\sqrt{cp}}{\sqrt{cp}}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L37) | [Verified](../SampLib/Bernoulli/TrigonometricSeriesFactories.lean) |
| `Occil.Constants.continuedLogarithm` | $\mathrm{Bern}\!\left(\cfrac{2^{-c_1}}{1+\cfrac{2^{-c_2}}{1+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L118) | [Verified](../SampLib/Constants/ContinuedLogarithm.lean) |
| `Occil.Constants.rationalContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1/d_1}{a_1/d_1+\cfrac{b_2/d_2}{a_2/d_2+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L98) | [Verified](../SampLib/Constants/FiniteRationalContinuedFraction.lean) |
| `Occil.Constants.eContinuedFraction` | $\mathrm{Bern}(p_j),\ p_j\text{ a continued-fraction tail}$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L76) | [Verified](../SampLib/Constants/EContinuedFraction.lean) |
| `Occil.Constants.eDivThree` | $\mathrm{Bern}\!\left(e/3\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L44) | [Verified](../SampLib/Constants/EulerScaledConstants.lean) |
| `Occil.Constants.eMinusTwo` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L27) | [Verified](../SampLib/Constants/EulerAffineConstants.lean) |
| `Occil.Constants.eMinusTwoContinuedFraction` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L89) | [Verified](../SampLib/Constants/EContinuedFractionConstants.lean) |
| `Occil.Constants.eQuarter` | $\mathrm{Bern}(e/4)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L131) | [Verified](../SampLib/Constants/EulerScaledConstants.lean) |
| `Occil.Constants.inverseEPlus` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L53) | [Verified](../SampLib/Constants/InverseEPlus.lean) |
| `Occil.Constants.inverseEPlusContinuedFraction` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L86) | [Verified](../SampLib/Constants/EContinuedFractionConstants.lean) |
| `Occil.Constants.tanhHalf` | $\mathrm{Bern}\!\left(\tanh(1/2)\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L93) | [Verified](../SampLib/Constants/TanhHalf.lean) |
| `Occil.Constants.threeMinusE` | $\mathrm{Bern}\!\left(3-e\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L46) | [Verified](../SampLib/Constants/EulerAffineConstants.lean) |
| `Occil.Constants.numericalEulerReciprocal` | $\mathsf{Grid}_s[\text{numerical Euler Reciprocal}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L35) | None; native-real port, grid proof excluded |
| `Occil.Constants.numericalExpRationalProduct` | $\mathsf{Grid}_s[\text{numerical Exp Rational Product}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L41) | None; native-real port, grid proof excluded |
| `Occil.Constants.numericalLogPiOverPi` | $\mathsf{Grid}_s[\text{numerical Log Pi Over Pi}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L48) | None; native-real port, grid proof excluded |
| `Occil.Constants.numericalLowerGammaRatio` | $\mathsf{Grid}_s[\text{numerical Lower Gamma Ratio}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L23) | None; native-real port, grid proof excluded |
| `Occil.Constants.numericalRationalPower` | $\mathsf{Grid}_s[\text{numerical Rational Power}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L15) | None; native-real port, grid proof excluded |
| `Occil.Constants.arctanRationalOverRatio` | $\mathrm{Bern}(\arctan(x/y)/(x/y))$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L94) | [Verified](../SampLib/Constants/ArctanRationalOverRatio.lean) |
| `Occil.Constants.fourOverThreePi` | $\mathrm{Bern}\!\left(4/(3\pi)\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L82) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.inversePi` | $\mathrm{Bern}\!\left(1/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L80) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.inverseSqrtPi` | $\mathrm{Bern}\!\left(1/\sqrt\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L91) | [Verified](../SampLib/Constants/InverseSqrtPi.lean) |
| `Occil.Constants.logPiOverPi` | $\mathrm{Bern}\!\left(\log\pi/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L85) | [Verified](../SampLib/Constants/LogPiOverPi.lean) |
| `Occil.Constants.piMinusThree` | $\mathrm{Bern}\!\left(\pi-3\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L66) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.piMinusThreeOverFour` | $\mathrm{Bern}\!\left((\pi-3)/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L64) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.piQuarter` | $\mathrm{Bern}\!\left(\pi/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L58) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.piQuarterMinusHalf` | $\mathrm{Bern}\!\left(\pi/4-1/2\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L62) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.piTwelfth` | $\mathrm{Bern}\!\left(\pi/12\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L60) | [Verified](../SampLib/Constants/PiConstants.lean) |
| `Occil.Constants.erfRatio` | $\mathrm{Bern}(\mathrm{erf}(x)/\mathrm{erf}(1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L76) | [Verified](../SampLib/Constants/ErfRatio.lean) |
| `Occil.Constants.eulerMascheroni` | $\mathrm{Bern}\!\left(\gamma\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L39) | [Verified](../SampLib/Constants/EulerMascheroni.lean) |
| `Occil.Constants.logOnePlusRational` | $\mathrm{Bern}\!\left(\log(1+x/y)\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L49) | [Verified](../SampLib/Constants/LogOnePlusRational.lean) |
| `Occil.Constants.lowerGammaIntegerRatio` | $\mathrm{Bern}(\gamma(m,x)/\gamma(m,1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L88) | [Verified](../SampLib/Constants/LowerGammaIntegerRatio.lean) |
| `Occil.Constants.rationalIntegerPower` | $\mathrm{Bern}\!\left((a/b)^n\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L53) | [Verified](../SampLib/Constants/RationalIntegerPower.lean) |
| `Occil.Constants.zetaRelated` | $\mathrm{Bern}\!\left(\zeta(k)(1-2^{1-k})\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L25) | [Verified](../SampLib/Constants/ZetaRelated.lean) |
| `Occil.arctanFactory` | $\mathrm{Bern}\!\left(\arctan(p)\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L111) | [Verified](../SampLib/Bernoulli/ArctanFactory.lean) |
| `Occil.arctanOverPFactory` | $\mathrm{Bern}\!\left(\arctan(p)/p\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L103) | [Verified](../SampLib/Bernoulli/ArctanOverPFactory.lean) |
| `Occil.sampleGeometricBag` | $\mathrm{Bern}(U)\ \text{with shared latent }U$ | [Lazy.lean](../code/Samplers/Lazy.lean#L53) | [Verified](../SampLib/Bernoulli/SampleGeometricBag.lean) |

## Additional Bernoulli implementation priorities

Implement the additional Bernoulli constructions in this order:

| Priority | Construction | Proposed module | Work and dependencies |
| --- | --- | --- | --- |
| 1 | Real-coefficient reverse-time envelopes | `Bernoulli/RealEnvelopes.lean` | Port `envelopeFactoryDegrees` from rational pairs to reals. Keep one sampled uniform and the exact conditional hypergeometric averaging and rescaling. |
| 1 | Hölder and Lipschitz envelope builders | `Bernoulli/EnvelopeBuilders.lean` | Supply the function callback, regularity constants, exponent, and domain and margin data. Use power-of-two degrees and the global fallback coefficients that the source prescribes. |
| 1 | Lipschitz-derivative builder | `Bernoulli/EnvelopeBuilders.lean` | Build a separate construction for smoother functions. Convex and concave specializations and endpoint factorization follow. |
| 2 | Dice Enterprise | `Bernoulli/DiceEnterprise.lean` | Compile homogeneous coefficients to the ladder, replay the shared coin and uniform history under monotone CFTP, and then select an output. Provide rational and real coefficient versions. |
| 2 | Polynomial preparation | `Bernoulli/DiceEnterprise.lean` | Homogenize and augment degrees. Accept coefficient data with explicit admissibility and termination conditions. Use no symbolic algebra oracle. |
| 3 | Multiple-output half-probability factory | `Bernoulli/MultipleOutput.lean` | Implement Occil's two-extractor recycling construction, including extractor state and output dependence tests. Independent repetition is not this algorithm. |
| 3 | Native-real known-constant coins | `Constants/Real.lean` | Build direct constructions from pi, log, exp, and powers, and the general positive-real lower-gamma rejection method. Keep these distinct from a factory for an unknown input coin. |

Sources: [rational functions and Dice Enterprise](https://peteroupc.github.io/bernoulli.html#certain-rational-functions),
[polynomial preparation](https://peteroupc.github.io/bernoulli.html#preparing-rational-functions),
[envelope builders](https://peteroupc.github.io/bernsupp.html#building-the-lower-and-upper-polynomials),
and [multiple outputs](https://peteroupc.github.io/bernsupp.html#multiple-output-bernoulli-factory).

Native reals newly enable one main factory component: real-valued envelope construction.
Dice Enterprise and recycling were already expressible with integers, coins, and heap
state. Preserve unknown input probabilities: receive a `coin : unit → bool` callback, never
its probability `p`. A direct `urand < f(p)` term is not a Bernoulli factory for an
unknown `p`.

## Native-real port order

Port the numerical samplers in this order:

1. Shared support: real constants, a guarded open-unit uniform, absolute value, explicit
   conversions between integers and reals, and a real power with an explicit zero-base
   branch. Upstream, `pow(0,y)` expands to `exp(y*log(0))`, so it cannot silently stand for
   ordinary nonnegative real powers.
2. The exponential inverse transform; Box-Muller, polar, and ratio-of-uniforms normals;
   Marsaglia-Tsang gamma and small-shape reduction; beta; and real-rate Poisson. These
   unlock most later ports.
3. Elementary inverse transforms and the families derived from gamma and normal, then
   mixtures and densities.
4. Geometry, linear algebra and Dirichlet, stable laws, phase-type distributions, and
   elementary copulas.
5. Generic quantile and CDF composition schemes, only with explicit in-language callbacks.
   A callback interface does not implement a missing normal CDF, Student CDF, or inverse
   CDF.

Use a separate `Samplers/Real/` tree (`Occil.Real`), and append imports rather than
rewrite the reviewed implementation files. Preserve the current APIs and the historical
proof receipts. Factor out shared real operations, but do not mechanically replace every
integer division with real division.

## Acceptance and tests

Follow these rules when you accept a new or ported term:

- Record the source section, parameter domain, and output law for every term. In the
  index, distinguish a new technique, a native-real port, and a derived wrapper.
- Build each new module and its closed fixtures at `Float` and at `ℝ`. Run the actual
  `pl%` terms through both interpreter paths with the existing sample runners and the JSON
  and IEEE-bit transport.
- For Bernoulli samplers, test parameter grids that include the endpoints that the source
  allows, analytic output probabilities, input-coin call counters, and fixtures for
  termination and invalid domains. Envelope tests must check that coefficients stay
  consistent under degree elevation; pointwise bounds alone fail.
- For real samplers, run support and nonfinite checks, analytic CDF or moment tests,
  dependence tests on paired coordinates, and fixtures at rejection boundaries. Keep
  integer shape and count parameters as integers.
- For multiple outputs, test joint frequencies and serial dependence in addition to
  marginal means.
- Float testing checks executable behavior; it does not certify the ideal-real law. No
  grid-error allowance should disguise a fixed-point computation that a claimed native-real
  port still keeps.
- Keep approximation-only normal CLT variants, finite quadrature, approximate CDF and
  quantile routines, and algorithms that are already invalid out of the exact-real queue.
- After implementations land, update `SamplerLaws.json`, and then regenerate `LAWS.md` and
  the README index. Proof work is a later queue and must follow `VerifyingSamplers.md`.

## Candidate inventory

These lists hold all **224 existing numerical catalog entries to triage**, not 224 promised
ports. The source files contain executable formulas and existing runtime fixtures. The lists
deliberately include approximation-only entries, so that they account for every omission
from the implementation queue. Each section keeps its current source group, and
native-real ports get new names.

### Constant coins: `Numerical` (5)

See the [current implementation](../code/Samplers/Constants/Numerical.lean).

- `Occil.Constants.numericalRationalPower`
- `Occil.Constants.numericalLowerGammaRatio`
- `Occil.Constants.numericalEulerReciprocal`
- `Occil.Constants.numericalExpRationalProduct`
- `Occil.Constants.numericalLogPiOverPi`

### Discrete distributions: `Numerical` (5)

See the [current implementation](../code/Samplers/Discrete/Numerical.lean).

- `Occil.DiscreteExtra.negativeBinomialNumerical`
- `Occil.DiscreteExtra.betaNegativeBinomialNumerical`
- `Occil.DiscreteExtra.bellTouchard`
- `Occil.DiscreteExtra.bell`
- `Occil.DiscreteExtra.discretePareto`

### Numerical multivariate algorithms: `Copulas` (21)

See the [current implementation](../code/Samplers/Multivariate/Copulas.lean).

- `Occil.Multivariate.gaussianCopula`
- `Occil.Multivariate.productCopula`
- `Occil.Multivariate.upperBoundCopula`
- `Occil.Multivariate.lowerBoundCopula`
- `Occil.Multivariate.normalToAnything`
- `Occil.Multivariate.correlatedExponential`
- `Occil.Multivariate.poissonHierarchy`
- `Occil.Multivariate.poissonHierarchyND`
- `Occil.Multivariate.studentT`
- `Occil.Multivariate.studentTCopula`
- `Occil.Multivariate.archimedeanCopula`
- `Occil.Multivariate.claytonCopula`
- `Occil.Multivariate.elliptical`
- `Occil.Multivariate.beckmann`
- `Occil.Multivariate.rice`
- `Occil.Multivariate.riceNorton`
- `Occil.Multivariate.complexNormal`
- `Occil.Multivariate.gumbelCopula`
- `Occil.Multivariate.exchangeableLabels`
- `Occil.Multivariate.exchangeableFGMSource`
- `Occil.Multivariate.exchangeableFGMCopula`

### Numerical multivariate algorithms: `Geometry` (20)

See the [current implementation](../code/Samplers/Multivariate/Geometry.lean).

- `Occil.Multivariate.uniformRange`
- `Occil.Multivariate.exponentialPower`
- `Occil.Multivariate.sphere`
- `Occil.Multivariate.ball`
- `Occil.Multivariate.ballEPD`
- `Occil.Multivariate.shell`
- `Occil.Multivariate.box`
- `Occil.Multivariate.hypercube`
- `Occil.Multivariate.cone`
- `Occil.Multivariate.cylinder`
- `Occil.Multivariate.circle`
- `Occil.Multivariate.cylinderSurface`
- `Occil.Multivariate.halfSphere`
- `Occil.Multivariate.halfBall`
- `Occil.Multivariate.halfShell`
- `Occil.Multivariate.latitudeLongitude`
- `Occil.Multivariate.simplex`
- `Occil.Multivariate.triangle`
- `Occil.Multivariate.ellipsoidSurface`
- `Occil.Multivariate.betaBall`

### Numerical multivariate algorithms: `Linear` (8)

See the [current implementation](../code/Samplers/Multivariate/Linear.lean).

- `Occil.Multivariate.standardNormals`
- `Occil.Multivariate.normal`
- `Occil.Multivariate.binormal`
- `Occil.Multivariate.dirichlet`
- `Occil.Multivariate.uniformPartition`
- `Occil.Multivariate.logNormal`
- `Occil.Multivariate.meanMixture`
- `Occil.Multivariate.meanVarianceMixture`

### Numerical multivariate algorithms: `PhaseType` (9)

See the [current implementation](../code/Samplers/Multivariate/PhaseType.lean).

- `Occil.Multivariate.initialPhase`
- `Occil.Multivariate.phaseType`
- `Occil.Multivariate.inhomogeneousPhaseType`
- `Occil.Multivariate.multivariatePhaseType`
- `Occil.Multivariate.phaseTypeRandomRewards`
- `Occil.Multivariate.inhomogeneousMultivariatePhaseType`
- `Occil.Multivariate.multivariateLinnik`
- `Occil.Multivariate.multivariateLinnikSource`
- `Occil.Multivariate.multivariateExponentialPower`

### Numerical multivariate algorithms: `Stable` (6)

See the [current implementation](../code/Samplers/Multivariate/Stable.lean).

- `Occil.Multivariate.stable`
- `Occil.Multivariate.geometricStable`
- `Occil.Multivariate.linnik`
- `Occil.Multivariate.mittagLeffler`
- `Occil.Multivariate.generalGeometricStable`
- `Occil.Multivariate.vonMises`

### Numerical arithmetic (2)

See the [current implementation](../code/Samplers/Numeric.lean).

- `Occil.Numeric.uniform`
- `Occil.Numeric.coin`

### Numerical grid algorithms: `Core` (2)

See the [current implementation](../code/Samplers/Numerical/Core.lean).

- `Occil.Numerical.uniformRange`
- `Occil.Numerical.exponential`

### Numerical grid algorithms: `Densities` (5)

See the [current implementation](../code/Samplers/Numerical/Densities.lean).

- `Occil.Numerical.hypoexponential`
- `Occil.Numerical.hyperexponential`
- `Occil.Numerical.piecewiseLinear`
- `Occil.Numerical.piecewiseConstant`
- `Occil.Numerical.sinePower`

### Numerical grid algorithms: `DistributionFamilies` (20)

See the [current implementation](../code/Samplers/Numerical/DistributionFamilies.lean).

- `Occil.Specialized.xG`
- `Occil.Specialized.expG`
- `Occil.Specialized.alphaPowerTransformed`
- `Occil.Specialized.exponentiatedG`
- `Occil.Specialized.transmutedG`
- `Occil.Specialized.cubicRankTransmuted`
- `Occil.Specialized.biweightG`
- `Occil.Specialized.transformedTransformer`
- `Occil.Specialized.tRY`
- `Occil.Specialized.oddXG`
- `Occil.Specialized.oddLogLogisticG`
- `Occil.Specialized.rayleighG`
- `Occil.Specialized.rayleighRayleigh`
- `Occil.Specialized.generalizedGammaG`
- `Occil.Specialized.inverseDistribution`
- `Occil.Specialized.weightedDistribution`
- `Occil.Specialized.inflatedDistribution`
- `Occil.Specialized.zeroOneInflated`
- `Occil.Specialized.unitDistribution`
- `Occil.Specialized.cdfQuantileFamily`

### Numerical grid algorithms: `Gamma` (3)

See the [current implementation](../code/Samplers/Numerical/Gamma.lean).

- `Occil.Numerical.gamma`
- `Occil.Numerical.beta`
- `Occil.Numerical.gammaSmallShape`

### Numerical grid algorithms: `GammaFamilies` (30)

See the [current implementation](../code/Samplers/Numerical/GammaFamilies.lean).

- `Occil.Numerical.chiSquared`
- `Occil.Numerical.noncentralChiSquared`
- `Occil.Numerical.studentT`
- `Occil.Numerical.fisherF`
- `Occil.Numerical.inverseGamma`
- `Occil.Numerical.kumaraswamy`
- `Occil.Numerical.betaPrime`
- `Occil.Numerical.betaPERT`
- `Occil.Numerical.noncentralBeta`
- `Occil.Numerical.chi`
- `Occil.Numerical.inverseChiSquared`
- `Occil.Numerical.levy`
- `Occil.Numerical.maxwell`
- `Occil.Numerical.wignerSemicircle`
- `Occil.Numerical.parabolic`
- `Occil.Numerical.arcsine`
- `Occil.Numerical.generalizedNormal`
- `Occil.Numerical.generalizedGamma`
- `Occil.Numerical.generalizedInverseGamma`
- `Occil.Numerical.powerDistribution`
- `Occil.Numerical.twinT`
- `Occil.Numerical.powerFunction`
- `Occil.Numerical.stacy`
- `Occil.Numerical.amoroso`
- `Occil.Numerical.pearsonVI`
- `Occil.Numerical.singhMaddala`
- `Occil.Numerical.dagum`
- `Occil.Numerical.logLogistic`
- `Occil.Numerical.minUniform`
- `Occil.Numerical.maxUniform`

### Numerical grid algorithms: `Mixtures` (19)

See the [current implementation](../code/Samplers/Numerical/Mixtures.lean).

- `Occil.Specialized.erlangMixture`
- `Occil.Specialized.lindley`
- `Occil.Specialized.garima`
- `Occil.Specialized.iGarima`
- `Occil.Specialized.weightedExponentialGamma`
- `Occil.Specialized.xgamma`
- `Occil.Specialized.mirra`
- `Occil.Specialized.sushila`
- `Occil.Specialized.xLindley`
- `Occil.Specialized.gammaExponential`
- `Occil.Specialized.extendedXgamma`
- `Occil.Specialized.skewSymmetric`
- `Occil.Specialized.logarithmicSkewNormal`
- `Occil.Specialized.twoPiece`
- `Occil.Specialized.asymmetricGeneralizedGaussian`
- `Occil.Specialized.offsetSymmetricGaussian`
- `Occil.Specialized.tiltedBeta`
- `Occil.Specialized.tiltedBetaBinomial`
- `Occil.Specialized.suzuki`

### Numerical grid algorithms: `Normal` (20)

See the [current implementation](../code/Samplers/Numerical/Normal.lean).

- `Occil.Numerical.normalBoxMuller`
- `Occil.Numerical.normalPolar`
- `Occil.Numerical.normal`
- `Occil.Numerical.normalRatioOfUniforms`
- `Occil.Numerical.normalInversion`
- `Occil.Numerical.normalCLT`
- `Occil.Numerical.lognormal`
- `Occil.Numerical.inverseGaussian`
- `Occil.Numerical.halfNormal`
- `Occil.Numerical.birnbaumSaunders`
- `Occil.Numerical.skewNormal`
- `Occil.Numerical.generalizedSkewNormal`
- `Occil.Numerical.moyal`
- `Occil.Numerical.powerNormal`
- `Occil.Numerical.powerLognormal`
- `Occil.Numerical.normalCLTWarped`
- `Occil.Numerical.normalCLTK`
- `Occil.Numerical.qGaussian`
- `Occil.Numerical.generalizedSkewNormalConditional`
- `Occil.Numerical.skewNormalExtremes`

### Numerical grid algorithms: `SpecialDistributions` (21)

See the [current implementation](../code/Samplers/Numerical/SpecialDistributions.lean).

- `Occil.Specialized.hyperbolicSecant`
- `Occil.Specialized.epanechnikov`
- `Occil.Specialized.ratioUniforms`
- `Occil.Specialized.reciprocalUniform`
- `Occil.Specialized.reciprocalPowerUniform`
- `Occil.Specialized.uniformOdds`
- `Occil.Specialized.arcCosine`
- `Occil.Specialized.exponentialLogRate`
- `Occil.Specialized.tulap`
- `Occil.Specialized.continuousBernoulli`
- `Occil.Specialized.powerFunction`
- `Occil.Specialized.lehmannWeibull`
- `Occil.Specialized.marshallOlkin`
- `Occil.Specialized.slash`
- `Occil.Specialized.lomax`
- `Occil.Specialized.powerLomax`
- `Occil.Specialized.toppLeone`
- `Occil.Specialized.generalizedPareto`
- `Occil.Specialized.quarterRectellipse`
- `Occil.Specialized.rectellipse`
- `Occil.Specialized.cosine`

### Numerical grid algorithms: `StoppedDistributions` (10)

See the [current implementation](../code/Samplers/Numerical/StoppedDistributions.lean).

- `Occil.Specialized.geometricZeroTruncatedPoisson`
- `Occil.Specialized.exponentialPoisson`
- `Occil.Specialized.poissonExponential`
- `Occil.Specialized.rightTruncatedWeibull`
- `Occil.Specialized.bivariateGammaGeometric`
- `Occil.Specialized.bivariateExponentialGeometric`
- `Occil.Specialized.unitLindley`
- `Occil.Specialized.zeroOneInflatedUnitLindley`
- `Occil.Specialized.grassia`
- `Occil.Specialized.gmdp`

### Numerical grid algorithms: `Univariate` (18)

See the [current implementation](../code/Samplers/Numerical/Univariate.lean).

- `Occil.Numerical.laplace`
- `Occil.Numerical.logistic`
- `Occil.Numerical.cauchy`
- `Occil.Numerical.cauchyDisk`
- `Occil.Numerical.weibull`
- `Occil.Numerical.pareto`
- `Occil.Numerical.rayleigh`
- `Occil.Numerical.gumbel`
- `Occil.Numerical.generalizedExtremeValue`
- `Occil.Numerical.frechet`
- `Occil.Numerical.triangular`
- `Occil.Numerical.triangularUniforms`
- `Occil.Numerical.tukeyLambda`
- `Occil.Numerical.generalizedTukeyLambda`
- `Occil.Numerical.powerLaw`
- `Occil.Numerical.logarithmicProduct`
- `Occil.Numerical.doubleLogarithmic`
- `Occil.Numerical.bates`

