# Native-real implementation queue

Prepared 2026-11-06 against `clutch-lean` `06a7b3e2`.
Implementation and verification planning: counts below are estimates, not new proofs or completeness claims.
No FFI and no new fixed-point/grid approximation work.

For the current request excluding all grid/numerical work, use the
[exact verification queue](ExactVerificationQueue.md): **137 existing unverified entries**.
The native-real port estimates below are separate and are not in that queue.

## Estimates

- **Existing Bernoulli backlog from `LAWS.md`: 68 entries without an accepted proof**:
  **33 ordinary factories + 3 lazy-coin samplers + 32 constant coins**. All 68 already have code.
  Five constant-coin entries are numerical; their native-real replacements belong in the port queue.
  That leaves **63 exact entries to assess individually**, not 6–10.
- Of those 63, `linearLowProbability` has a known-false advertised law and
  `sampleGeometricBag` already has a supporting coin theorem. Neither is a straightforward new
  standalone proof. The remaining **61 are the initial proof-candidate list**, subject to domain
  checks (including the continued-fraction divergence finding). Budget for roughly **45–60 useful
  proof completions**, with substantial shared mathematics; this is not a guarantee of success.
- **Additional Bernoulli implementations:** roughly **6–10 shared construction entry points**,
  plus named specializations after a source-by-source audit. This is an engine estimate, not
  the size of the missing Bernoulli sampler/proof backlog. It does not establish source completeness.
- **Native-real ports:** roughly **170–200 useful sampler entry points**, drawn from the 224
  numerical catalogue entries listed below. This includes native-real versions of existing
  techniques, not 170–200 previously absent algorithms. Exclude arithmetic helpers, CLT
  approximations, duplicate wrappers and constructions still requiring unavailable exact CDFs.
- Track these three queues separately: proofs of current terms, additional factory algorithms,
  and native-real ports. Do not add proof counts to implementation counts. Estimates concern scope;
  no elapsed-time estimate before representative implementations and proofs.

## Existing Bernoulli proof backlog (68)

Copied by individual entry from the current `LAWS.md`, including constant and lazy coins.
Every row has implementation code already. The proof column's dash means no accepted
standalone proof in the index, not missing implementation. New real primitives do not prove the
existing series, lazy-state or permutation constructions automatically. Verify their actual terms;
do not substitute a direct known-probability coin and call it the same proof.

| Entry | Intended law | Code | Next action |
| --- | --- | --- | --- |
| `Occil.fractionalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Basic.lean](../code/Samplers/Bernoulli/Basic.lean#L51) | Proof candidate; check domain |
| `Occil.FactoryExtra.complementOverLogInverse` | $\mathrm{Bern}\!\left(\frac{1-p}{\log(1/p)}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L107) | Proof candidate; check domain |
| `Occil.FactoryExtra.expIntegral` | $\mathrm{Bern}\!\left(\frac{1-e^{-(m+p)}}{m+p}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L71) | Proof candidate; check domain |
| `Occil.FactoryExtra.pOverLogInverseComplement` | $\mathrm{Bern}\!\left(\frac p{\log(1/(1-p))}\right)$ | [Elementary.lean](../code/Samplers/Bernoulli/Elementary.lean#L101) | Proof candidate; check domain |
| `Occil.FactoryExtra.binaryExponential` | $\mathrm{Bern}\!\left(2^{-m(k+p)}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L88) | Proof candidate; check domain |
| `Occil.FactoryExtra.binaryExponentialRational` | $\mathrm{Bern}\!\left(2^{-ap/b}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L98) | Proof candidate; check domain |
| `Occil.FactoryExtra.expDivThree` | $\mathrm{Bern}\!\left(e^p/3\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L65) | Proof candidate; check domain |
| `Occil.FactoryExtra.expMinusExp` | $\mathrm{Bern}\!\left(e^{-e^{m+p}}\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L72) | Proof candidate; check domain |
| `Occil.FactoryExtra.expSquareTimesComplement` | $\mathrm{Bern}\!\left(e^{p^2}(1-p)\right)$ | [Exponential.lean](../code/Samplers/Bernoulli/Exponential.lean#L82) | Proof candidate; check domain |
| `Occil.FactoryExtra.linear2014` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L129) | Proof candidate; check domain |
| `Occil.FactoryExtra.linearLowProbability` | $\mathrm{Bern}\!\left(cp\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L93) | Repair first: advertised law is false |
| `Occil.FactoryExtra.linearPowerWalk` | $\mathrm{Bern}\!\left((cp)^m\right)$ | [Linear.lean](../code/Samplers/Bernoulli/Linear.lean#L108) | Proof candidate; check domain |
| `Occil.FactoryExtra.polynomial` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L19) | Proof candidate; check domain |
| `Occil.FactoryExtra.rationalFunction` | $\mathrm{Bern}\!\left(f(p)/g(p)\right)$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L48) | Proof candidate; check domain |
| `Occil.FactoryExtra.threePointPiecewise` | $\mathrm{Bern}(f(p)),\ f\text{ piecewise affine}$ | [Polynomials.lean](../code/Samplers/Bernoulli/Polynomials.lean#L57) | Proof candidate; check domain |
| `Occil.FactoryExtra.rationalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L15) | Proof candidate; check domain |
| `Occil.FactoryExtra.twoCoinPower` | $\mathrm{Bern}\!\left(p^q\right)$ | [Powers.lean](../code/Samplers/Bernoulli/Powers.lean#L24) | Proof candidate; check domain |
| `Occil.FactoryExtra.alternatingSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}(-1)^nc_np^n\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L20) | Proof candidate; check domain |
| `Occil.FactoryExtra.envelopeFactory` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L118) | Proof candidate; check domain |
| `Occil.FactoryExtra.envelopeFactoryDegrees` | $\mathrm{Bern}\!\left(f(p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L79) | Proof candidate; check domain |
| `Occil.FactoryExtra.minimumComplement` | $\mathrm{Bern}\!\left(\min(p,1-p)\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L135) | Proof candidate; check domain |
| `Occil.FactoryExtra.minimumHalf` | $\mathrm{Bern}(\min(p,1/2))$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L150) | Proof candidate; check domain |
| `Occil.FactoryExtra.powerSeriesHazards` | $\mathrm{Bern}\!\left(1-\sum_{n\ge0}c_n(1-p)^{n+1}\right)$ | [Series.lean](../code/Samplers/Bernoulli/Series.lean#L50) | Proof candidate; check domain |
| `Occil.FactoryExtra.alternatingPermutation` | $\mathrm{Bern}\!\left(\begin{cases}(1-p)/\cos p&r=0\\(1-p)\tan p&r=1\end{cases}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L47) | Proof candidate; check domain |
| `Occil.FactoryExtra.arcsineHalf` | $\mathrm{Bern}\!\left(\frac12\arcsin p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L81) | Proof candidate; check domain |
| `Occil.FactoryExtra.arcsinePlusSqrtMinusOne` | $\mathrm{Bern}\!\left(\arcsin p+\sqrt{1-p^2}-1\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L69) | Proof candidate; check domain |
| `Occil.FactoryExtra.arctanOverPi` | $\mathrm{Bern}\!\left(\arctan(p)/\pi\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L32) | Proof candidate; check domain |
| `Occil.FactoryExtra.complementOverCosine` | $\mathrm{Bern}\!\left(\frac{1-p}{\cos p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L61) | Proof candidate; check domain |
| `Occil.FactoryExtra.complementTimesTangent` | $\mathrm{Bern}\!\left((1-p)\tan p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L64) | Proof candidate; check domain |
| `Occil.FactoryExtra.cosineSqrt` | $\mathrm{Bern}\!\left(\cos\sqrt p\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L26) | Proof candidate; check domain |
| `Occil.FactoryExtra.pOverTangent` | $\mathrm{Bern}\!\left(\frac p{\tan p}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L88) | Proof candidate; check domain |
| `Occil.FactoryExtra.sincScaled` | $\mathrm{Bern}\!\left(\frac{\sin(p\sqrt c)}{p\sqrt c}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L17) | Proof candidate; check domain |
| `Occil.FactoryExtra.sincSqrtScaled` | $\mathrm{Bern}\!\left(\frac{\sin\sqrt{cp}}{\sqrt{cp}}\right)$ | [Trigonometric.lean](../code/Samplers/Bernoulli/Trigonometric.lean#L37) | Proof candidate; check domain |
| `Occil.Constants.continuedLogarithm` | $\mathrm{Bern}\!\left(\cfrac{2^{-c_1}}{1+\cfrac{2^{-c_2}}{1+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L118) | Proof candidate; check domain |
| `Occil.Constants.rationalContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1/d_1}{a_1/d_1+\cfrac{b_2/d_2}{a_2/d_2+\cdots}}\right)$ | [Engines.lean](../code/Samplers/Constants/Engines.lean#L98) | Restrict domain: unrestricted version may diverge |
| `Occil.Constants.eContinuedFraction` | $\mathrm{Bern}(p_j),\ p_j\text{ a continued-fraction tail}$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L76) | Proof candidate; check domain |
| `Occil.Constants.eDivThree` | $\mathrm{Bern}\!\left(e/3\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L44) | Proof candidate; check domain |
| `Occil.Constants.eMinusTwo` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L27) | Proof candidate; check domain |
| `Occil.Constants.eMinusTwoContinuedFraction` | $\mathrm{Bern}\!\left(e-2\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L89) | Proof candidate; check domain |
| `Occil.Constants.eQuarter` | $\mathrm{Bern}(e/4)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L131) | Proof candidate; check domain |
| `Occil.Constants.inverseEPlus` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L53) | Proof candidate; check domain |
| `Occil.Constants.inverseEPlusContinuedFraction` | $\mathrm{Bern}((e+c-2)^{-1})$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L86) | Proof candidate; check domain |
| `Occil.Constants.tanhHalf` | $\mathrm{Bern}\!\left(\tanh(1/2)\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L93) | Proof candidate; check domain |
| `Occil.Constants.threeMinusE` | $\mathrm{Bern}\!\left(3-e\right)$ | [Exponential.lean](../code/Samplers/Constants/Exponential.lean#L46) | Proof candidate; check domain |
| `Occil.Constants.numericalEulerReciprocal` | $\mathsf{Grid}_s[\text{numerical Euler Reciprocal}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L35) | Native-real port; grid proof excluded |
| `Occil.Constants.numericalExpRationalProduct` | $\mathsf{Grid}_s[\text{numerical Exp Rational Product}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L41) | Native-real port; grid proof excluded |
| `Occil.Constants.numericalLogPiOverPi` | $\mathsf{Grid}_s[\text{numerical Log Pi Over Pi}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L48) | Native-real port; grid proof excluded |
| `Occil.Constants.numericalLowerGammaRatio` | $\mathsf{Grid}_s[\text{numerical Lower Gamma Ratio}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L23) | Native-real port; grid proof excluded |
| `Occil.Constants.numericalRationalPower` | $\mathsf{Grid}_s[\text{numerical Rational Power}]$ | [Numerical.lean](../code/Samplers/Constants/Numerical.lean#L15) | Native-real port; grid proof excluded |
| `Occil.Constants.arctanRationalOverRatio` | $\mathrm{Bern}(\arctan(x/y)/(x/y))$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L94) | Proof candidate; check domain |
| `Occil.Constants.fourOverThreePi` | $\mathrm{Bern}\!\left(4/(3\pi)\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L82) | Proof candidate; check domain |
| `Occil.Constants.inversePi` | $\mathrm{Bern}\!\left(1/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L80) | Proof candidate; check domain |
| `Occil.Constants.inverseSqrtPi` | $\mathrm{Bern}\!\left(1/\sqrt\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L91) | Proof candidate; check domain |
| `Occil.Constants.logPiOverPi` | $\mathrm{Bern}\!\left(\log\pi/\pi\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L85) | Proof candidate; check domain |
| `Occil.Constants.piMinusThree` | $\mathrm{Bern}\!\left(\pi-3\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L66) | Proof candidate; check domain |
| `Occil.Constants.piMinusThreeOverFour` | $\mathrm{Bern}\!\left((\pi-3)/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L64) | Proof candidate; check domain |
| `Occil.Constants.piQuarter` | $\mathrm{Bern}\!\left(\pi/4\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L58) | Proof candidate; check domain |
| `Occil.Constants.piQuarterMinusHalf` | $\mathrm{Bern}\!\left(\pi/4-1/2\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L62) | Proof candidate; check domain |
| `Occil.Constants.piTwelfth` | $\mathrm{Bern}\!\left(\pi/12\right)$ | [Pi.lean](../code/Samplers/Constants/Pi.lean#L60) | Proof candidate; check domain |
| `Occil.Constants.erfRatio` | $\mathrm{Bern}(\mathrm{erf}(x)/\mathrm{erf}(1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L76) | Proof candidate; check domain |
| `Occil.Constants.eulerMascheroni` | $\mathrm{Bern}\!\left(\gamma\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L39) | Proof candidate; check domain |
| `Occil.Constants.logOnePlusRational` | $\mathrm{Bern}\!\left(\log(1+x/y)\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L49) | Proof candidate; check domain |
| `Occil.Constants.lowerGammaIntegerRatio` | $\mathrm{Bern}(\gamma(m,x)/\gamma(m,1))$ | [Special.lean](../code/Samplers/Constants/Special.lean#L88) | Proof candidate; check domain |
| `Occil.Constants.rationalIntegerPower` | $\mathrm{Bern}\!\left((a/b)^n\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L53) | Proof candidate; check domain |
| `Occil.Constants.zetaRelated` | $\mathrm{Bern}\!\left(\zeta(k)(1-2^{1-k})\right)$ | [Special.lean](../code/Samplers/Constants/Special.lean#L25) | Proof candidate; check domain |
| `Occil.arctanFactory` | $\mathrm{Bern}\!\left(\arctan(p)\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L111) | Proof candidate; check domain |
| `Occil.arctanOverPFactory` | $\mathrm{Bern}\!\left(\arctan(p)/p\right)$ | [Lazy.lean](../code/Samplers/Lazy.lean#L103) | Proof candidate; check domain |
| `Occil.sampleGeometricBag` | $\mathrm{Bern}(U)\ \text{with shared latent }U$ | [Lazy.lean](../code/Samplers/Lazy.lean#L53) | Supporting coin theorem exists; audit index/spec interface |

## Additional Bernoulli implementation priorities

| Priority | Construction / proposed module | Work and dependency |
| --- | --- | --- |
| 1 | Real-coefficient reverse-time envelopes / `Bernoulli/RealEnvelopes.lean` | Port `envelopeFactoryDegrees` from rational pairs to reals. Keep one sampled uniform and the exact conditional hypergeometric averaging/rescaling. |
| 1 | Hölder and Lipschitz envelope builders / `Bernoulli/EnvelopeBuilders.lean` | Supply function callback, regularity constants, exponent and domain/margin data. Use power-of-two degrees and source-prescribed global fallback coefficients. |
| 1 | Lipschitz-derivative builder / same module | Separate smoother-function construction; convex/concave specializations and endpoint factorization follow. |
| 2 | Dice Enterprise / `Bernoulli/DiceEnterprise.lean` | Compile homogeneous coefficients to the ladder, replay shared coin/uniform history under monotone CFTP, then select an output. Rational and real coefficient versions. |
| 2 | Polynomial preparation / same module | Homogenization and degree augmentation; accept coefficient data, with explicit admissibility/termination conditions. No symbolic algebra oracle. |
| 3 | Multiple-output half-probability factory / `Bernoulli/MultipleOutput.lean` | Implement Occil's two-extractor recycling construction, including extractor state and output dependence tests. Independent repetition is not this algorithm. |
| 3 | Native-real known-constant coins / `Constants/Real.lean` | Direct constructions using pi/log/exp/powers, and the general positive-real lower-gamma rejection method. Keep distinct from an unknown-input-coin factory. |

Source anchors: [rational functions / Dice Enterprise](https://peteroupc.github.io/bernoulli.html#certain-rational-functions),
[polynomial preparation](https://peteroupc.github.io/bernoulli.html#preparing-rational-functions),
[envelope builders](https://peteroupc.github.io/bernsupp.html#building-the-lower-and-upper-polynomials),
[multiple outputs](https://peteroupc.github.io/bernsupp.html#multiple-output-bernoulli-factory).

The main newly enabled factory component is real-valued envelope construction. Dice Enterprise
and recycling were already expressible with integers, coins and heap state. Preserve unknown
input probabilities: receive a `coin : unit → bool` callback, never its probability `p`.
A direct `urand < f(p)` term is not a Bernoulli factory for an unknown `p`.

## Native-real port order

1. Shared support: real constants, guarded open-unit uniform, absolute value, explicit integer/real
   conversions, real power with an explicit zero-base branch. Upstream `pow(0,y)` expands to
   `exp(y*log(0))`, so it cannot silently stand for ordinary nonnegative real powers.
2. Exponential inverse transform; Box–Muller, polar and ratio-of-uniforms normals; Marsaglia–Tsang
   gamma and small-shape reduction; beta and real-rate Poisson. These unlock most downstream ports.
3. Elementary inverse transforms and gamma/normal-derived families, then mixtures and densities.
4. Geometry, linear algebra/Dirichlet, stable laws, phase-type distributions and elementary copulas.
5. Generic quantile/CDF composition schemes only with explicit in-language callbacks. A callback
   interface is not an implementation of a missing normal CDF, Student CDF or inverse CDF.

Use a separate `Samplers/Real/` tree (`Occil.Real`) and append imports rather than rewriting the
reviewed implementation files. Preserve current APIs and historical proof receipts. Factor shared
real operations; do not mechanically replace every integer division with real division.

## Acceptance and tests

- Record source section, parameter domain and output law for every term. Distinguish a new
  technique, a native-real port and a derived wrapper in the index.
- Build each new module and closed fixtures at `Float` and `ℝ`; run actual `pl%` terms through
  both interpreter paths using the existing sample runners and JSON/IEEE-bit transport.
- Bernoulli tests: parameter grids including endpoints allowed by the source, analytic output
  probabilities, input-coin call counters, and termination/invalid-domain fixtures. Envelope
  tests must check coefficient consistency under degree elevation; pointwise bounds alone fail.
- Real samplers: support and nonfinite checks, analytic CDF or moment tests, paired-coordinate
  dependence tests, and rejection-boundary fixtures. Keep integer shape/count parameters integer.
- Multiple outputs: test joint frequencies and serial dependence in addition to marginal means.
- Float testing checks executable behavior; it does not certify the ideal-real law. No grid-error
  allowance should disguise a retained fixed-point computation in a claimed native-real port.
- Keep approximation-only normal CLT variants, finite quadrature, approximate CDF/quantile
  routines and already invalid algorithms out of the exact-real queue. In particular, do not
  port `linearLowProbability` under its known-false advertised law.
- Update `SamplerLaws.json`, regenerate `LAWS.md` and the README index after implementations
  land. Proof work is a later queue and must follow `VerifyingSamplers.md`.

## Candidate inventory

These are all **224 existing numerical catalogue entries to triage**, not 224 promised ports.
The source files contain executable formulas and existing runtime fixtures. Names below include
approximation-only entries deliberately, so that omissions from the implementation queue are
accounted for. Module rows retain their current source groups; native-real ports get new names.

### Constant coins / Numerical (5)

[Current implementation](../code/Samplers/Constants/Numerical.lean).

- `Occil.Constants.numericalRationalPower`
- `Occil.Constants.numericalLowerGammaRatio`
- `Occil.Constants.numericalEulerReciprocal`
- `Occil.Constants.numericalExpRationalProduct`
- `Occil.Constants.numericalLogPiOverPi`

### Discrete distributions / Numerical (5)

[Current implementation](../code/Samplers/Discrete/Numerical.lean).

- `Occil.DiscreteExtra.negativeBinomialNumerical`
- `Occil.DiscreteExtra.betaNegativeBinomialNumerical`
- `Occil.DiscreteExtra.bellTouchard`
- `Occil.DiscreteExtra.bell`
- `Occil.DiscreteExtra.discretePareto`

### Numerical multivariate algorithms / Copulas (21)

[Current implementation](../code/Samplers/Multivariate/Copulas.lean).

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

### Numerical multivariate algorithms / Geometry (20)

[Current implementation](../code/Samplers/Multivariate/Geometry.lean).

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

### Numerical multivariate algorithms / Linear (8)

[Current implementation](../code/Samplers/Multivariate/Linear.lean).

- `Occil.Multivariate.standardNormals`
- `Occil.Multivariate.normal`
- `Occil.Multivariate.binormal`
- `Occil.Multivariate.dirichlet`
- `Occil.Multivariate.uniformPartition`
- `Occil.Multivariate.logNormal`
- `Occil.Multivariate.meanMixture`
- `Occil.Multivariate.meanVarianceMixture`

### Numerical multivariate algorithms / PhaseType (9)

[Current implementation](../code/Samplers/Multivariate/PhaseType.lean).

- `Occil.Multivariate.initialPhase`
- `Occil.Multivariate.phaseType`
- `Occil.Multivariate.inhomogeneousPhaseType`
- `Occil.Multivariate.multivariatePhaseType`
- `Occil.Multivariate.phaseTypeRandomRewards`
- `Occil.Multivariate.inhomogeneousMultivariatePhaseType`
- `Occil.Multivariate.multivariateLinnik`
- `Occil.Multivariate.multivariateLinnikSource`
- `Occil.Multivariate.multivariateExponentialPower`

### Numerical multivariate algorithms / Stable (6)

[Current implementation](../code/Samplers/Multivariate/Stable.lean).

- `Occil.Multivariate.stable`
- `Occil.Multivariate.geometricStable`
- `Occil.Multivariate.linnik`
- `Occil.Multivariate.mittagLeffler`
- `Occil.Multivariate.generalGeometricStable`
- `Occil.Multivariate.vonMises`

### Numerical arithmetic (2)

[Current implementation](../code/Samplers/Numeric.lean).

- `Occil.Numeric.uniform`
- `Occil.Numeric.coin`

### Numerical grid algorithms / Core (2)

[Current implementation](../code/Samplers/Numerical/Core.lean).

- `Occil.Numerical.uniformRange`
- `Occil.Numerical.exponential`

### Numerical grid algorithms / Densities (5)

[Current implementation](../code/Samplers/Numerical/Densities.lean).

- `Occil.Numerical.hypoexponential`
- `Occil.Numerical.hyperexponential`
- `Occil.Numerical.piecewiseLinear`
- `Occil.Numerical.piecewiseConstant`
- `Occil.Numerical.sinePower`

### Numerical grid algorithms / DistributionFamilies (20)

[Current implementation](../code/Samplers/Numerical/DistributionFamilies.lean).

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

### Numerical grid algorithms / Gamma (3)

[Current implementation](../code/Samplers/Numerical/Gamma.lean).

- `Occil.Numerical.gamma`
- `Occil.Numerical.beta`
- `Occil.Numerical.gammaSmallShape`

### Numerical grid algorithms / GammaFamilies (30)

[Current implementation](../code/Samplers/Numerical/GammaFamilies.lean).

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

### Numerical grid algorithms / Mixtures (19)

[Current implementation](../code/Samplers/Numerical/Mixtures.lean).

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

### Numerical grid algorithms / Normal (20)

[Current implementation](../code/Samplers/Numerical/Normal.lean).

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

### Numerical grid algorithms / SpecialDistributions (21)

[Current implementation](../code/Samplers/Numerical/SpecialDistributions.lean).

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

### Numerical grid algorithms / StoppedDistributions (10)

[Current implementation](../code/Samplers/Numerical/StoppedDistributions.lean).

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

### Numerical grid algorithms / Univariate (18)

[Current implementation](../code/Samplers/Numerical/Univariate.lean).

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

