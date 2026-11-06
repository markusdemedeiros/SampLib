# Constants

This directory holds the proofs for coins of named constants, which digit and interval engines produce.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (45)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.Constants.algebraicRoot` | $\mathrm{Bern}\!\left(\alpha,\ f(\alpha)=0\right)$ | [AlgebraicRoot](AlgebraicRoot.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L132) |
| `Occil.Constants.arctanRationalOverRatio` | $\mathrm{Bern}(\arctan(x/y)/(x/y))$ | [ArctanRationalOverRatio](ArctanRationalOverRatio.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L94) |
| `Occil.Constants.continuedFraction` | $\mathrm{Bern}\!\left(\cfrac1{a_1+\cfrac1{a_2+\cdots}}\right)$ | [ContinuedFraction](ContinuedFraction.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L112) |
| `Occil.Constants.continuedLogarithm` | $\mathrm{Bern}\!\left(\cfrac{2^{-c_1}}{1+\cfrac{2^{-c_2}}{1+\cdots}}\right)$ | [ContinuedLogarithm](ContinuedLogarithm.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L118) |
| `Occil.Constants.eContinuedFraction` | $\mathrm{Bern}(p_j),\ p_j\text{ a continued-fraction tail}$ | [EContinuedFraction](EContinuedFraction.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L76) |
| `Occil.Constants.eDivThree` | $\mathrm{Bern}\!\left(e/3\right)$ | [EulerScaledConstants](EulerScaledConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L44) |
| `Occil.Constants.eMinusTwo` | $\mathrm{Bern}\!\left(e-2\right)$ | [EulerAffineConstants](EulerAffineConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L27) |
| `Occil.Constants.eMinusTwoContinuedFraction` | $\mathrm{Bern}\!\left(e-2\right)$ | [EContinuedFractionConstants](EContinuedFractionConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L89) |
| `Occil.Constants.eOverPi` | $\mathrm{Bern}\!\left(e/\pi\right)$ | [EOverPi](EOverPi.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L61) |
| `Occil.Constants.eQuarter` | $\mathrm{Bern}(e/4)$ | [EulerScaledConstants](EulerScaledConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L131) |
| `Occil.Constants.eScaled` | $\mathrm{Bern}(en/d)$ | [EScaled](EScaled.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L34) |
| `Occil.Constants.erfRatio` | $\mathrm{Bern}(\mathrm{erf}(x)/\mathrm{erf}(1))$ | [ErfRatio](ErfRatio.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L76) |
| `Occil.Constants.eulerMascheroni` | $\mathrm{Bern}\!\left(\gamma\right)$ | [EulerMascheroni](EulerMascheroni.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L39) |
| `Occil.Constants.exponentialRationalProduct` | $\mathrm{Bern}(e^{-x/y}z/t)$ | [ExponentialRationalProduct](ExponentialRationalProduct.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L121) |
| `Occil.Constants.fourOverThreePi` | $\mathrm{Bern}\!\left(4/(3\pi)\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L82) |
| `Occil.Constants.fromApproximateDigits` | $\mathrm{Bern}\!\left(p\right)$ | [FromApproximateDigits](FromApproximateDigits.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L30) |
| `Occil.Constants.fromBounds` | $\mathrm{Bern}\!\left(p\right)$ | [FromBounds](FromBounds.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L44) |
| `Occil.Constants.fromDigits` | $\mathrm{Bern}\!\left(\sum_{k\ge1}d_kb^{-k}\right)$ | [FromDigits](FromDigits.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L18) |
| `Occil.Constants.fromPositiveSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}a_n/b_n\right)$ | [FromPositiveSeries](FromPositiveSeries.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L59) |
| `Occil.Constants.generalizedContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1}{a_1+\cfrac{b_2}{a_2+\cdots}}\right)$ | [GeneralizedContinuedFraction](GeneralizedContinuedFraction.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L84) |
| `Occil.Constants.goldenFamily` | $\mathrm{Bern}\!\left(\left(\frac{m+\sqrt{m^2+4\ell}}2\right)^{-k}\right)$ | [GoldenFamily](GoldenFamily.lean) | [Algebraic.lean](../../code/Samplers/Constants/Algebraic.lean#L30) |
| `Occil.Constants.inverseEPlus` | $\mathrm{Bern}((e+c-2)^{-1})$ | [InverseEPlus](InverseEPlus.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L53) |
| `Occil.Constants.inverseEPlusContinuedFraction` | $\mathrm{Bern}((e+c-2)^{-1})$ | [EContinuedFractionConstants](EContinuedFractionConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L86) |
| `Occil.Constants.inverseEPlusRational` | $\mathrm{Bern}((e+c-2)^{-1})$ | [InverseEPlusRational](InverseEPlusRational.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L64) |
| `Occil.Constants.inverseGoldenRatio` | $\mathrm{Bern}\!\left((\sqrt5-1)/2\right)$ | [InverseGoldenRatio](InverseGoldenRatio.lean) | [Algebraic.lean](../../code/Samplers/Constants/Algebraic.lean#L19) |
| `Occil.Constants.inversePi` | $\mathrm{Bern}\!\left(1/\pi\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L80) |
| `Occil.Constants.inverseSqrtPi` | $\mathrm{Bern}\!\left(1/\sqrt\pi\right)$ | [InverseSqrtPi](InverseSqrtPi.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L91) |
| `Occil.Constants.inverseSqrtTwo` | $\mathrm{Bern}\!\left(1/\sqrt2\right)$ | [InverseSqrtTwo](InverseSqrtTwo.lean) | [Algebraic.lean](../../code/Samplers/Constants/Algebraic.lean#L25) |
| `Occil.Constants.logOnePlusRational` | $\mathrm{Bern}\!\left(\log(1+x/y)\right)$ | [LogOnePlusRational](LogOnePlusRational.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L49) |
| `Occil.Constants.logPiOverPi` | $\mathrm{Bern}\!\left(\log\pi/\pi\right)$ | [LogPiOverPi](LogPiOverPi.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L85) |
| `Occil.Constants.lowerGammaIntegerRatio` | $\mathrm{Bern}(\gamma(m,x)/\gamma(m,1))$ | [LowerGammaIntegerRatio](LowerGammaIntegerRatio.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L88) |
| `Occil.Constants.piAffine` | $\mathrm{Bern}((\pi-a)/b)$ | [PiAffine](PiAffine.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L49) |
| `Occil.Constants.piMinusThree` | $\mathrm{Bern}\!\left(\pi-3\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L66) |
| `Occil.Constants.piMinusThreeOverFour` | $\mathrm{Bern}\!\left((\pi-3)/4\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L64) |
| `Occil.Constants.piQuarter` | $\mathrm{Bern}\!\left(\pi/4\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L58) |
| `Occil.Constants.piQuarterMinusHalf` | $\mathrm{Bern}\!\left(\pi/4-1/2\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L62) |
| `Occil.Constants.piTwelfth` | $\mathrm{Bern}\!\left(\pi/12\right)$ | [PiConstants](PiConstants.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L60) |
| `Occil.Constants.rationalContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1/d_1}{a_1/d_1+\cfrac{b_2/d_2}{a_2/d_2+\cdots}}\right)$ | [FiniteRationalContinuedFraction](FiniteRationalContinuedFraction.lean) | [Engines.lean](../../code/Samplers/Constants/Engines.lean#L98) |
| `Occil.Constants.rationalIntegerPower` | $\mathrm{Bern}\!\left((a/b)^n\right)$ | [RationalIntegerPower](RationalIntegerPower.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L53) |
| `Occil.Constants.reciprocalPiScaled` | $\mathrm{Bern}\!\left(a/(b\pi)\right)$ | [ReciprocalPiScaled](ReciprocalPiScaled.lean) | [Pi.lean](../../code/Samplers/Constants/Pi.lean#L69) |
| `Occil.Constants.sqrtTwoMinusOne` | $\mathrm{Bern}\!\left(\sqrt2-1\right)$ | [SqrtTwoMinusOne](SqrtTwoMinusOne.lean) | [Algebraic.lean](../../code/Samplers/Constants/Algebraic.lean#L22) |
| `Occil.Constants.tanhHalf` | $\mathrm{Bern}\!\left(\tanh(1/2)\right)$ | [TanhHalf](TanhHalf.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L93) |
| `Occil.Constants.threeMinusE` | $\mathrm{Bern}\!\left(3-e\right)$ | [EulerAffineConstants](EulerAffineConstants.lean) | [Exponential.lean](../../code/Samplers/Constants/Exponential.lean#L46) |
| `Occil.Constants.threeZetaThreeOverFour` | $\mathrm{Bern}\!\left(3\zeta(3)/4\right)$ | [ThreeZetaThreeOverFour](ThreeZetaThreeOverFour.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L18) |
| `Occil.Constants.zetaRelated` | $\mathrm{Bern}\!\left(\zeta(k)(1-2^{1-k})\right)$ | [ZetaRelated](ZetaRelated.lean) | [Special.lean](../../code/Samplers/Constants/Special.lean#L25) |

## Contents

- Top level: 39 modules
- [`Laws/`](Laws): 33 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 1 modules with unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 8 modules with CTE loop invariants and other program-level helpers

---

`python3 agent-scripts/law_index.py` generates this file.
