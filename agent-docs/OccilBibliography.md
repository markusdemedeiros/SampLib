# Bibliography of the sources behind Occil's sampling articles

This document lists the books and papers that Peter Occil's sampling articles cite. For each source, it gives the full citation, whether a legal free copy exists, the algorithms that Occil takes from it, and whether this repository implements each one. The goal is to guide the next set of samplers to add.

## How this document was built

I fetched these articles on 2026-11-06: `randomfunc.html`, `randomnotes.html`, `bernoulli.html`, `bernsupp.html`, `exporand.html`, `randmisc.html`, `randextract.html`, and `bernapprox.html`. I read their reference lists and the sentences that cite each reference. I then checked each algorithm against `LAWS.md`, `code/README.md`, and the sampler index in `README.md`.

These limits apply to every section:

- I read only Occil's articles. I did not read the cited books and papers. Each summary repeats what Occil says the source contributes, in my own words, and Occil may simplify or adapt the original.
- A URL marked as checked returned HTTP status 200 on 2026-11-06. A URL marked as not verified came from Occil's reference list or from a DOI, and I did not confirm that it gives free access.
- I list only free copies that the author or publisher provides. I did not look for other copies.
- Occil does not cite volume 2 of Knuth's "The Art of Computer Programming" and does not cite Kennedy. The only Knuth reference is the 1976 paper by Knuth and Yao, covered in its own section.
- The sampler index in `README.md` lags `LAWS.md`. For example, the index shows no code for Knuth-Yao, Han-Hoshi, Fast Loaded Dice Roller, and Vose, but `LAWS.md` lists all four. I treat `LAWS.md` as the authority and cite the sampler name from it.
- `LAWS.md` marks many samplers as numerical grid algorithms. These approximate their target law, so I count them as implementing the formula but not the exact algorithm where the difference matters. I note each such case.

A status of "Implemented" means that a sampler in `LAWS.md` follows the cited algorithm or an equivalent exact one. "Partly implemented" means that the repository covers a special case, a numerical variant, or the same law by a different method. "Missing" means that I found no matching sampler.

## Devroye, Non-Uniform Random Variate Generation

**Citation.** Devroye, L., "Non-Uniform Random Variate Generation", Springer, 1986.

**Availability.** The author hosts a free PDF at https://luc.devroye.org/rnbookindex.html (checked). I did not consult the book itself.

Occil cites the book mostly for classic textbook methods and for page-level facts. The following table lists the algorithms, with page numbers as Occil gives them.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Sequential search for a discrete distribution (inverse transform), p. 85 and chapter 10 | `randomfunc`, weighted choice | Implemented (`weightedChoice`, `Weighted.cumulativeChoice`, `General.discreteCDF`) |
| Choosing k items in list order, p. 620 | `randomfunc`, RandomKItemsInOrder | Implemented (`sampleInOrder`) |
| Poisson as a sum of exponential waiting times, p. 504 | `randomfunc`, Poisson distribution | Missing (`poissonRational` samples the same law with a different method) |
| Thinning a Poisson variate with binomial trials, p. 487 | `randomfunc`, PoissonInt; `bernoulli`, exp(-x) factories | Implemented (`poissonRational`, `FactoryExtra.expMinusScaled`) |
| Geometric variate and the negative binomial convention, pp. 498 and 500 | `randomfunc`, geometric distribution | Implemented (`geometric`, `negativeBinomial`) |
| Order statistics of uniform variates, pp. 210 and 675 | `randomfunc`, kth-order statistic, min and max of uniforms | Implemented (`orderStatistic`, `uniformMax`, `uniformMin`) |
| Rejection sampling, pp. 41 to 43 | `randomfunc`, rejection sampling | Implemented (`rejection`, `General.pdfRejection`) |
| Rejection with a dominated squeeze function, p. 53 | `randomfunc`, rejection with a PDF-like function | Partly implemented (`General.shapeRejection` covers the plain form) |
| Weighted distribution by acceptance with probability w(x), p. 47 | `randmisc`, weighted distributions | Implemented (`Specialized.weightedDistribution`) |
| Piecewise linear variate from a uniform and a maximum of two uniforms, pp. 71 and 72 | `randmisc`, piecewise linear distribution | Implemented (`General.piecewiseLinear`) |
| Digit-by-digit generation from an infinite digit expansion, p. 769 | `bernoulli`, `exporand`, digit expansion coins | Implemented (`Constants.fromDigits`, `Constants.fromBounds`) |
| Zeta distribution by rejection, pp. 174 and 175 | `randomfunc`, zeta distribution | Implemented (`DiscreteExtra.zeta`) |
| Logarithmic series distribution | `randomfunc`, logarithmic distribution | Implemented (`DiscreteExtra.logarithmicSeries`) |
| Beta as a ratio of gamma variates; small-shape accuracy warning, p. 675 | `randomfunc`, BetaDist | Partly implemented (`Numerical.beta` is a grid algorithm; `PSRN.newBeta` is exact for shapes of at least 1) |

## Devroye, later papers

**Citations.**
- Devroye, L., "Random variate generation in one line of code", Proceedings of the 28th Winter Simulation Conference, 1996, https://doi.org/10.1145/256562.256623.
- Devroye, L., "Non-Uniform Random Variate Generation", in Handbooks in Operations Research and Management Science: Simulation, 2006.
- Devroye, L., "Expected time analysis of a simple recursive Poisson random variate generator", Computing 46, 1991, https://doi.org/10.1007/BF02239170.

**Availability.** The 2006 chapter is at https://luc.devroye.org/handbooksimulation1.pdf (checked). I found no free copy of the 1996 and 1991 papers and did not consult them.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Short closed-form generators for common distributions (1996) | `randomfunc`, distribution index | Partly implemented (`Numerical.studentT`, `Numerical.cauchy`, and others are grid algorithms) |
| Order statistic through the quantile of a beta variate (2006) | `randomfunc`, inverse transform sampling | Implemented (`orderStatistic`, `General.inverseQuantile`) |
| Recursive Poisson generator (1991) | `randomfunc`, Poisson distribution | Missing |

## Knuth and Yao, "The complexity of nonuniform random number generation"

**Citation.** Knuth, D. E., and Yao, A. C.-C., "The complexity of nonuniform random number generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.

**Availability.** I found no free copy. I did not consult the paper. Occil cites it without any link to a full text.

Occil uses the paper for the discrete distribution generating (DDG) tree model and its entropy bounds. The following table lists the cited items.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| DDG tree sampler built from the binary expansions of the probabilities | `randomfunc`, weighted choice comparison | Implemented (`Weighted.knuthYao`) |
| Optimal uniform integer in an interval, using between log2(n) and log2(n) + 2 bits on average | `randomfunc`, RNDINT as a tree walker | Implemented (`fastDiceRoller`) |
| Binary tree that returns 1 with a given rational probability | `bernsupp`, optimal factories | Implemented (`rationalCoin`) |
| Finite-state generators of random variates, and their link to algebraic functions | `bernsupp`, finite-state and pushdown generators | Missing |
| Entropy lower bound on bits per sample | `bernoulli`, `exporand`, `randmisc` | Not an algorithm; no sampler needed |

## Flajolet, Pelletier, and Soria, "On Buffon machines and numbers"

**Citation.** Flajolet, P., Pelletier, M., and Soria, M., "On Buffon machines and numbers", arXiv:0906.5560 [math.PR], 2010.

**Availability.** Free at https://arxiv.org/abs/0906.5560 (checked).

This is the most cited source on the Bernoulli factory pages. Occil takes many constructions from it.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Complement, product (AND), disjunction (OR), and mean of coins | `bernoulli`, elementary composition | Implemented (`complement`, `coinProduct`, `coinDisjunction`, `coinMean`) |
| Conditional construction, a mixture of two coins by a third | `bernoulli`, conditional | Implemented (`coinConditional`) |
| Even-parity construction for 1/(1+lambda) | `bernoulli`, even-parity | Implemented (`evenParity`, `oneDivOnePlus`) |
| Square-root construction for sqrt(1-lambda) | `bernoulli`, sqrt | Implemented (`fractionalPower`, composed with `complement`) |
| Geometric bag, a lazily sampled uniform number | `bernoulli`, `exporand` | Implemented (`sampleGeometricBag`, `PSRN.fillGeometricBag`) |
| Von Neumann schema, with examples for exp(-lambda) and exp(lambda)(1-lambda) | `bernoulli`, series | Implemented (`expMinusFactory`, `FactoryExtra.expTimesComplement`) |
| Algorithm BR on permutation classes, such as alternating permutations, for sin, cos, and tan | `bernoulli`, `bernsupp` | Implemented (`sineFactory`, `cosineFactory`, `FactoryExtra.alternatingPermutation`) |
| Arctangent and pi-related Buffon needle constants | `bernoulli`, constants | Implemented (`arctanFactory`, `Constants.piQuarter`) |
| Polylogarithm and logarithmic series coins | `bernoulli`, `randomfunc` | Implemented (`FactoryExtra.polylogarithm`, `DiscreteExtra.logarithmicSeries`) |
| Algebraic functions through context-free grammars, binary stochastic grammars, ternary trees | `bernoulli`, algebraic functions; `bernsupp`, pushdown generators | Missing |
| Probability simulation schemes beyond the ones above | `bernoulli`, Flajolet's schemes | Partly implemented (`FactoryExtra.integralMixture`, `FactoryExtra.alternatingPermutation`) |

## Flajolet and Saheb, "The complexity of generating an exponentially distributed variate"

**Citation.** Flajolet, P., and Saheb, N., "The complexity of generating an exponentially distributed variate", Research Report RR-0159, INRIA, 1982.

**Availability.** Not verified. INRIA research reports usually have a copy on HAL, but I did not locate this one.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Exponential variate from random bits | `exporand`, introduction to exponential PSRNs | Partly implemented (`exponential` and `PSRN.newExponential` give the same law with other methods) |

## Thomas and Luk, "Sampling from the exponential distribution using independent Bernoulli variates"

**Citation.** Thomas, D. B., and Luk, W., "Sampling from the exponential distribution using independent Bernoulli variates", International Conference on Field Programmable Logic and Applications, September 2008.

**Availability.** I found no free copy and did not consult the paper.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Exponential variate from independent Bernoulli trials, with a bit-driven comparison structure | `exporand`, introduction and comparison of PSRN methods | Partly implemented (`PSRN.newExponential` covers the law; the Bernoulli-trial construction is missing) |

## Keane and O'Brien, "A Bernoulli factory"

**Citation.** Keane, M. S., and O'Brien, G. L., "A Bernoulli factory", ACM Transactions on Modeling and Computer Simulation 4(2), 1994, https://doi.org/10.1145/175007.175019.

**Availability.** The publisher page was not verified as free. I did not consult the paper.

Occil cites the paper for the problem statement and the existence theorem, not for a specific algorithm.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Existence criterion: a function has a factory when it is continuous and polynomially bounded away from 0 and 1 | `bernoulli`, `bernsupp`, table of factory functions | Not an algorithm; the repository states the criteria in its domains |
| Factory for 2 * lambda on [0, 1/2 - epsilon] | `bernoulli`, linear factories | Implemented (`FactoryExtra.linear`, `FactoryExtra.linear2014`) |
| Original construction that handles any such function, with unbounded expected cost | `bernoulli`, general factory functions | Partly implemented (`FactoryExtra.envelopeFactoryDegrees` is a bounded-cost general construction) |

## Nacu and Peres, "Fast simulation of new coins from old"

**Citation.** Nacu, S., and Peres, Y., "Fast simulation of new coins from old", The Annals of Applied Probability 15(1A), 2005, pp. 93 to 115, https://doi.org/10.1214/105051604000000549.

**Availability.** Free at https://arxiv.org/abs/math/0309222 (checked) and on Project Euclid (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Bernstein-envelope factory with polynomial sequences that converge from below and above | `bernoulli`, general factory functions; `bernapprox` | Implemented (`FactoryExtra.envelopeFactoryDegrees`, `FactoryExtra.envelopeFactory`) |
| Sum of two coins, lambda + mu (proposition 14 iii) | `bernoulli`, probability-sensitive factories | Missing |
| Mean of coins (proposition 14 iii) | `bernoulli`, mean | Implemented (`coinMean`) |
| Power-series factory when the coefficients sum to more than 1 (proposition 16) | `bernoulli`, power series | Partly implemented (`FactoryExtra.positivePowerSeries` takes normalized coefficients) |
| Rounding rule for rational parameters in the exp and power constructions | `bernoulli`, rational parameters | Implemented (`FactoryExtra.expMinusScaled`) |

## Mossel and Peres, "New coins from old: computing with unknown bias"

**Citation.** Mossel, E., and Peres, Y., "New coins from old: computing with unknown bias", Combinatorica 25(6), 2005, pp. 707 to 724, with an appendix by C. Hillar, https://doi.org/10.1007/s00493-005-0043-1.

**Availability.** Free at https://arxiv.org/abs/math/0304143 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Rational functions with 0 < f < 1 inside (0, 1), using degree elevation of Bernstein coefficients | `bernoulli`, certain rational functions | Partly implemented (`FactoryExtra.rationalFunction` handles the form A/(A+B) with polynomial parts) |
| Algebraic functions as solutions of polynomial equations, by finite-state and pushdown machines | `bernoulli`, algebraic functions; `bernsupp`, appendix | Missing |
| Block simulation with extraction of leftover randomness (proposition 2.5) | `bernsupp`, optimal factory notes | Missing |
| Unbiased estimators and exact sampling (section 4) | `bernoulli`, notes | Not an algorithm |

## Holtz, Nazarov, and Peres, "New coins from old, smoothly"

**Citation.** Holtz, O., Nazarov, F., and Peres, Y., "New coins from old, smoothly", Constructive Approximation 33, 2011.

**Availability.** Free at https://arxiv.org/abs/0808.1936 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Conditions under which a smooth function has a factory, and a degree-doubling bound for the polynomial envelopes (lemma 4) | `bernoulli`, `bernsupp`, `bernapprox` | Implemented (`FactoryExtra.envelopeFactoryDegrees`) |
| Lorentz and Bernstein polynomial constructions that give fast-converging envelopes | `bernapprox`, polynomial sequences | Missing (the envelope sequences are caller-supplied; the repository does not build them) |
| Scaling the envelope constants for input coins that can return only 1 or only 0 | `bernoulli`, general factory functions | Partly implemented |

## Thomas and Blanchet, "A Practical Implementation of the Bernoulli Factory"

**Citation.** Thomas, A. C., and Blanchet, J., "A Practical Implementation of the Bernoulli Factory", arXiv:1106.2508v3 [stat.AP], 2012.

**Availability.** Free at https://arxiv.org/abs/1106.2508 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Factory for a quadratic polynomial with a constant factor, as a worked example | `bernoulli`, polynomials | Implemented (`bernsteinFactory`, `FactoryExtra.polynomial`) |
| Rational-function factory in the style of Mossel and Peres | `bernoulli`, rational functions | Partly implemented (`FactoryExtra.rationalFunction`) |
| Factory with several pairs of polynomial sequences | `bernoulli`, notes | Missing |
| Improvement of the Nacu-Peres algorithm | `bernoulli`, general factory functions | Missing |

## Goyal and Sigman, "On simulating a class of Bernstein polynomials"

**Citation.** Goyal, V., and Sigman, K., "On simulating a class of Bernstein polynomials", ACM Transactions on Modeling and Computer Simulation 22(2), Article 12, 2012, https://doi.org/10.1145/2133390.2133396.

**Availability.** Not verified. I did not consult the paper.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Fixed-flip factory for Bernstein polynomials with coefficients in [0, 1] | `bernoulli`, `bernsupp`, polynomials | Implemented (`bernsteinFactory`) |
| Poisson-variate version of the same construction | `bernsupp` | Missing |

## Wästlund, "Functions arising by coin flipping"

**Citation.** Wästlund, J., "Functions arising by coin flipping", 1999.

**Availability.** Free at https://www.math.chalmers.se/~wastlund/coinFlip.pdf (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Race of several coins with a random number of rounds (theorem 2.7), including an infinite round count | `bernoulli`, Bernoulli race and generalizations | Partly implemented (`bernoulliRace` handles two coins; `probabilityGeneratingFactory` covers the Poisson count) |
| Poisson count, then flips of the input coin, for E[1/(1+X)] | `bernoulli`, `exp`-related factories | Implemented (`probabilityGeneratingFactory`, `FactoryExtra.expIntegral`) |
| Polynomial families such as (lambda(1-lambda))^k scaled by binomial weights | `bernoulli`, sine and cosine notes | Partly implemented |
| Fixed-flip factories exist only for polynomials of a certain kind (section 4) | `bernoulli`, polynomials | Not an algorithm |

## Huber, three papers on linear factories and perfect simulation

**Citations.**
- Huber, M., "Nearly optimal Bernoulli factories for linear functions", arXiv:1308.1562v2 [math.PR], 2014.
- Huber, M., "Optimal linear Bernoulli factories for small mean problems", arXiv:1507.00843v2 [math.PR], 2016.
- Huber, M., "Designing perfect simulation algorithms using local correctness", arXiv:1907.06748v1 [cs.DS], 2019.

**Availability.** All three are free on arXiv: https://arxiv.org/abs/1308.1562, https://arxiv.org/abs/1507.00843, and https://arxiv.org/abs/1907.06748 (checked). The book "Perfect Simulation" by Huber is not cited by Occil.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Expanding linear factory for c * lambda with a margin epsilon (2014) | `bernoulli`, linear Bernoulli factories | Implemented (`FactoryExtra.linear2014`) |
| Linear factory for (a/b) * lambda, a second 2016 variant | `bernoulli`, linear Bernoulli factories | Implemented (`FactoryExtra.linear`) |
| Logistic factory c * lambda / (c * lambda + d) | `bernoulli`, two-coin algorithm | Implemented (`logisticFactory`, `FactoryExtra.twoCoin`) |
| Linear factory for a sum of several input coins, c0 * lambda0 + c1 * lambda1 + ... | `bernoulli`, multivariate linear | Missing |
| Linear factory for lambda * x/y when the product is known to stay below 1 (2016, third algorithm) | `bernoulli`, linear factories | Partly implemented (`FactoryExtra.linearLowProbability`) |
| Joint linear and power factory (lambda * x/y)^i (2019) | `bernoulli`, power factories | Implemented (`FactoryExtra.linearPowerWalk`) |
| Local-correctness design method for perfect simulation | `bernoulli`, notes | Missing |
| Poisson point process view of the logistic factory | `bernoulli`, notes | Missing |

## Mendo, two papers on power series and irrational coins

**Citations.**
- Mendo, L., "An asymptotically optimal Bernoulli factory for certain functions that can be expressed as power series", Stochastic Processes and their Applications 129(11), 2019, https://doi.org/10.1016/j.spa.2018.11.017.
- Mendo, L., "Simulating a coin with irrational bias using rational arithmetic", Communications in Statistics, Simulation and Computation, 2024.

**Availability.** Not verified for either paper. Occil says the 2024 paper also appears as a preprint, but I did not confirm the identifier.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Power-series factory for coefficient sums of at most 1, types 1 to 4 | `bernoulli`, power series (algorithm 2 and Mendo's algorithm) | Implemented (`FactoryExtra.powerSeriesHazards`, `FactoryExtra.complementPowerSeries`) |
| Power of a coin, lambda^(x/y), with reciprocal-hazard trials | `bernoulli`, `lambda^(x/y)` | Implemented (`fractionalPower`) |
| Two-coin power, lambda^mu | `bernoulli`, probability-sensitive factories | Implemented (`FactoryExtra.twoCoinPower`) |
| Factory for exp(lambda)(1-lambda) as a type 1 series | `bernoulli`, example 11 | Implemented (`FactoryExtra.expTimesComplement`) |
| General algorithm for any probability given as a converging series with computable bounds | `bernoulli`, certain converging series | Implemented (`Constants.fromPositiveSeries`, `Constants.fromBounds`) |
| Euler-Mascheroni constant coin | `bernoulli`, constants | Implemented (`Constants.eulerMascheroni`) |

## Łatuszyński, Kosmidis, Papaspiliopoulos, and Roberts, "Simulating events of unknown probabilities via reverse time martingales"

**Citation.** Łatuszyński, K., Kosmidis, I., Papaspiliopoulos, O., and Roberts, G. O., "Simulating events of unknown probabilities via reverse time martingales", arXiv:0907.4018v2 [stat.CO], 2009 and 2011.

**Availability.** Free at https://arxiv.org/abs/0907.4018 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| General martingale algorithm with a polynomial or series bound | `bernoulli`, general martingale algorithm | Implemented (`expMinusMartingale`, `FactoryExtra.alternatingSeries`, `FactoryExtra.envelopeFactoryDegrees`) |
| Alternating-series coin for exp(-lambda) and similar functions | `bernoulli`, series | Implemented (`factorialSeriesFactory`) |

## Morina, Łatuszyński, Nayar, and Wendland, "From the Bernoulli factory to a dice enterprise"

**Citations.**
- Morina, G., Łatuszyński, K., Nayar, P., and Wendland, A., "From the Bernoulli factory to a dice enterprise via perfect sampling of Markov chains", Annals of Applied Probability 32(1), 2022, https://doi.org/10.1214/21-AAP1679.
- Morina, G., "Extending the Bernoulli Factory to a dice enterprise", PhD thesis, University of Warwick, 2021.

**Availability.** The paper is free at https://arxiv.org/abs/1912.09229 (checked). I did not locate the thesis.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Dice enterprise: simulate a categorical distribution whose probabilities are homogeneous polynomials of input coins | `bernoulli`, dice enterprise; `randextract` | Missing |
| Monotonic coupling from the past inside the dice enterprise | `bernoulli`, dice enterprise | Missing (`General.couplingFromPast` exists as a generic tool) |
| Degree augmentation of polynomials to meet the homogeneity conditions | `bernoulli`, dice enterprise | Missing |
| Logistic Bernoulli factory as a special case | `bernoulli`, two-coin algorithm | Implemented (`logisticFactory`) |
| Division factory mu / lambda (thesis) | `bernoulli`, probability-sensitive factories | Implemented (`FactoryExtra.division`, `FactoryExtra.epsilonDivision`) |

## Schmon, Doucet, and Deligiannidis, "Bernoulli race particle filters"

**Citation.** Schmon, S. M., Doucet, A., and Deligiannidis, G., "Bernoulli race particle filters", Proceedings of the 22nd International Conference on Artificial Intelligence and Statistics, 2019.

**Availability.** Not verified. The conference publishes proceedings in the PMLR series, but I did not confirm the URL.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Bernoulli race: choose among several coins in proportion to their probabilities, with a finite or infinite round limit | `bernoulli`, Bernoulli race and generalizations | Partly implemented (`bernoulliRace` handles two coins only) |

## Dughmi, Hartline, Kleinberg, and Niazadeh, "Bernoulli factories and black-box reductions in mechanism design"

**Citation.** Dughmi, S., Hartline, J., Kleinberg, R. D., and Niazadeh, R., "Bernoulli factories and black-box reductions in mechanism design", Journal of the ACM 68(2), Article 10, 2021, https://doi.org/10.1145/3440988.

**Availability.** Free at https://arxiv.org/abs/1703.04143 (checked). Occil also cites Niazadeh, Paes Leme, and Schneider, "Combinatorial Bernoulli factories", which is free at https://arxiv.org/abs/2011.03865 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Probability generating function factory: draw a count N, then require N successes | `bernoulli`, probability generating function | Implemented (`probabilityGeneratingFactory`) |
| Factories for matchings, flows, and polytopes (Niazadeh and others) | `bernoulli`, notes | Missing |

## Karney, "Sampling exactly from the normal distribution"

**Citation.** Karney, C. F. F., "Sampling exactly from the normal distribution", ACM Transactions on Mathematical Software 42(1), 2016, pp. 1 to 14.

**Availability.** Free at https://arxiv.org/abs/1303.6257 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Algorithm N: exact standard normal from comparisons, with an integer part and a fraction | `randomnotes`, normal distribution; `exporand`, normal PSRN | Implemented (`gaussian`, `gaussianInteger`, `PSRN.gaussianSelector`, `PSRN.newGaussian`) |
| u-rands: partially sampled uniform numbers, and comparison of a u-rand with a rational | `exporand`, PSRN basics | Implemented (`PSRN.newUniform`, `PSRN.less`, `uniformBagLess`) |
| Negation and integer-part operations on PSRNs | `exporand`, PSRN arithmetic | Implemented (`PSRN.negate`) |
| Definition of an exact algorithm with user-specified error bounds | `randomfunc`, `exporand` | Not an algorithm |

## Canonne, Kamath, and Steinke, "The Discrete Gaussian for Differential Privacy"

**Citation.** Canonne, C., Kamath, G., and Steinke, T., "The Discrete Gaussian for Differential Privacy", arXiv:2004.00010 [cs.DS], 2020.

**Availability.** Free at https://arxiv.org/abs/2004.00010 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Discrete Laplace sampler from Bernoulli(exp(-x/y)) trials and geometric variates | `bernoulli`, exp(-lambda) factories; `randmisc`, discrete distributions | Implemented (`DiscreteExtra.discreteLaplace`) |
| Discrete Gaussian sampler by rejection from the discrete Laplace | `bernoulli`, `randmisc` | Missing |

## Du, Fan, and Wei, "An improved exact sampling algorithm for the standard normal distribution"

**Citation.** Du, Y., Fan, B., and Wei, B., "An improved exact sampling algorithm for the standard normal distribution", Computational Statistics, 2021; arXiv:2008.03855.

**Availability.** Free at https://arxiv.org/abs/2008.03855 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Faster exact normal sampler that improves on Karney's Algorithm N | `randomnotes`, `exporand`, normal distribution | Missing |
| Early rejection for exponential variates (Fan and others, 2019) | `exporand`, introduction | Missing |

## Lumbroso, "Optimal discrete uniform generation from coin flips, and applications"

**Citation.** Lumbroso, J., "Optimal discrete uniform generation from coin flips, and applications", arXiv:1304.1916 [cs.DS], 2013.

**Availability.** Free at https://arxiv.org/abs/1304.1916 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Fast Dice Roller | `randomfunc`, RNDINT | Implemented (`fastDiceRoller`) |
| Bernoulli trial with probability px/py from fair bits (appendix B) | `randomfunc`, ZeroOrOne; `exporand` | Implemented (`rationalCoin`) |

## Saad, Freer, Rinard, and Mansinghka, two papers on discrete samplers

**Citations.**
- Saad, F. A., Freer, C. E., Rinard, M. C., and Mansinghka, V. K., "The Fast Loaded Dice Roller: A Near-Optimal Exact Sampler for Discrete Probability Distributions", arXiv:2003.03830v2 [stat.CO], AISTATS 2020.
- Saad, F. A., Freer, C. E., Rinard, M. C., and Mansinghka, V. K., "Optimal Approximate Sampling from Discrete Probability Distributions", arXiv:2001.04555v1 [cs.DS], POPL 2020.

**Availability.** Both are free: https://arxiv.org/abs/2003.03830 and https://arxiv.org/abs/2001.04555 (checked).

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Fast Loaded Dice Roller | `randomfunc`, weighted choice comparison | Implemented (`Weighted.fastLoadedDiceRoller`) |
| Optimal approximate sampler with a fixed bit budget | `randomfunc`, `randomnotes`, weighted choice | Implemented (`WeightedVariants.optimalChoice`, `WeightedVariants.optimalDraw`) |

## Duchon and Duvignau, "Preserving the number of cycles of length k in a growing uniform permutation"

**Citation.** Duchon, P., and Duvignau, R., "Preserving the number of cycles of length k in a growing uniform permutation", The Electronic Journal of Combinatorics 23(4), #P4.22, 2016, https://doi.org/10.37236/6014.

**Availability.** The journal is open access. I did not fetch the paper.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Poisson(1) variate from a small integer state machine that uses no real arithmetic | `randomfunc`, PoissonInt | Implemented (`poissonOne`, `poissonRational`) |

## Von Neumann and the extraction literature

**Citations.**
- Von Neumann, J., "Various techniques used in connection with random digits", NBS Applied Mathematics Series 12, 1951, pp. 36 to 38.
- Peres, Y., "Iterating von Neumann's procedure for extracting random bits", Annals of Statistics 20(1), 1992, pp. 590 to 597, https://doi.org/10.1214/aos/1176348543.
- Pae, S., "Random number generation using a biased source", dissertation, University of Illinois at Urbana-Champaign, 2005.
- Pae, S., "Binarization trees and random number generation", arXiv:1602.06058v2 [cs.DS], 2018.
- Pae, S., and Loui, M. C., "Randomizing functions: simulation of a discrete probability distribution using a source of unknown distribution", IEEE Transactions on Information Theory 52(11), 2006, https://doi.org/10.1109/TIT.2006.883555.
- Zhou, H., and Bruck, J., "Streaming algorithms for optimal generation of random bits", arXiv:1209.0730 [cs.IT], 2012.
- Camion, P., "Unbiased die rolling with a biased die", North Carolina State University, Department of Statistics, 1974.
- Kozen, D., "Optimal coin flipping", 2014.

**Availability.** Free copies that I checked: Pae 2018 at https://arxiv.org/abs/1602.06058, Zhou and Bruck at https://arxiv.org/abs/1209.0730, and Kozen at https://www.cs.cornell.edu/~kozen/Papers/Coinflip.pdf. I found no free copy of the 1951, 1974, and 2005 works, and did not verify the Peres 1992 or Pae and Loui copies.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Von Neumann extractor: fair bit from pairs of flips of a biased coin | `randextract`, `bernoulli`, `bernsupp`, `randmisc` | Implemented (`vonNeumann`) |
| Von Neumann method for exponential variates by decreasing-chain parity | `randomfunc`, `exporand` | Implemented (`exponential`, `expMinusFactory`) |
| Iterated von Neumann extractor (Peres) | `randextract`, `bernoulli`, `bernsupp`, `randmisc` | Missing |
| Optimal streaming extractor (Zhou and Bruck) | `randextract`, `randmisc` | Missing |
| Binarization trees and entropy-preserving binarization (Pae) | `randextract`, `bernsupp` | Missing |
| Randomizing functions that simulate a discrete law from an unknown source (Pae and Loui) | `randextract` | Missing |
| Die rolling with a biased die (Camion) | `randextract` | Missing |
| Optimal coin flipping, a construction of a coin of any bias from a fair or biased coin (Kozen) | `bernoulli`, `randextract` | Missing |
| Entropy bound for a factory from lambda to f(lambda) | `bernoulli`, notes | Not an algorithm |

## Devroye and Gravel, and Brassard, Devroye, and Gravel

**Citations.**
- Devroye, L., and Gravel, C., "Random variate generation using only finitely many unbiased, independently and identically distributed random bits", arXiv:1502.02539v6 [cs.IT], 2020.
- Brassard, G., Devroye, L., and Gravel, C., "Remote sampling with applications to general entanglement simulation", Entropy 21(92), 2019, https://doi.org/10.3390/e21010092.

**Availability.** Free at https://arxiv.org/abs/1502.02539 and https://arxiv.org/abs/1807.06649 (both checked). Entropy is an open-access journal.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Exact sampling of continuous variates from random bits, including exponential variates | `exporand`, `randextract`, `randomnotes` | Partly implemented (`PSRN.newExponential`, `PSRN.newGaussian`) |
| Batching and bit recycling for uniform integers (section 2.3) | `randomfunc`, RNDINT | Implemented (`Weighted.recycledUniform`) |
| Coin whose probability is a function of a lazily sampled uniform number | `exporand`, SampleGeometricBag | Implemented (`sampleGeometricBag`) |
| Remote sampling of distributions through partial digit information | `bernoulli`, `exporand` | Missing |

## Propp and Wilson, and Fill

**Citations.**
- Propp, J. G., and Wilson, D. B., "Exact sampling with coupled Markov chains and applications to statistical mechanics", Random Structures and Algorithms 9, 1996, pp. 223 to 252.
- Fill, J. A., "An interruptible algorithm for perfect sampling via Markov chains", Annals of Applied Probability 8(1), 1998, https://doi.org/10.1214/aoap/1027961037.

**Availability.** Not verified for either paper. Occil gives a Project Euclid link for Fill, but I did not confirm free access.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Coupling from the past | `randomfunc`, Markov chains; `bernoulli`, dice enterprise | Implemented (`General.couplingFromPast`, `General.perfectFiniteChain`) |
| Fill's interruptible algorithm | `randomfunc`, Markov chains | Missing |

## Other cited sources with one algorithm each

These sources appear in one or two places. The following table gives each source in the Algorithm column, because each contributes a single algorithm.

| Algorithm | Where Occil cites it | Status |
| --- | --- | --- |
| Mennucci, "Bit recycling for scaling random number generators": recycle leftover randomness, arXiv:1012.4290 (free, checked) | `randomfunc`, RNDINT | Implemented (`Weighted.recycledUniform`) |
| Bacher, Bodini, Hwang, and Tsai, FYKY shuffle (ACM Transactions on Algorithms 13(2), 2017; not verified as free) | `randomfunc`, uniform integer comparison | Implemented (`Weighted.fyky`) |
| Bacher, Bodini, and others, "MergeShuffle", arXiv:1508.03167 (free, checked) | `randomfunc`, shuffling | Missing |
| Lemire, "Fast random integer generation in an interval", arXiv:1805.10941 (free, checked) | `randomfunc`, uniform integer comparison | Implemented (`WeightedVariants.lemireUniform`, `Weighted.multiplyShift`) |
| O'Neill, bitmask with rejection and the modulo-debiasing survey (blog post) | `randomfunc`, uniform integer comparison | Implemented (`WeightedVariants.oneillUniform`, `Weighted.bitmaskRejection`) |
| Sattolo single-cycle permutation, Python notes | `randomfunc`, permutations | Implemented (`sattolo`) |
| Merlini, Sprugnoli, and Verri, uniform derangements by rejection | `randomfunc`, derangements | Implemented (`derangement`) |
| Ting, "Simple, optimal algorithms for random sampling without replacement", arXiv:2104.05091 (free, checked) | `randomfunc`, sampling without replacement | Missing |
| Sanders, Lamm, and others, "Efficient parallel random sampling", arXiv:1610.05141 (free, checked) | `randomfunc`, sampling | Missing |
| Bentley and Saxe, "Generating sorted lists of random numbers" (ACM Transactions on Mathematical Software 6, 1980) | `randomfunc`, sorted uniform variates | Partly implemented (`orderStatistic` gives one order statistic, not the sorted list) |
| Walker alias method (ACM Transactions on Mathematical Software 3, 1977) | `randomfunc`, weighted choice comparison | Implemented (`aliasSamples`) |
| Vose, "A linear algorithm for generating random numbers with a given distribution" (1991) | `randomfunc`, weighted choice comparison | Implemented (`WeightedVariants.voseDraw`, `WeightedVariants.voseTable`) |
| Han and Hoshi, interval algorithm (IEEE Transactions on Information Theory 43, 1997) | `randomfunc`, weighted choice comparison | Implemented (`Weighted.hanHoshi`) |
| Bringmann and Larsen, succinct sampling from discrete distributions (STOC 2013) | `randomfunc`, weighted choice | Implemented (`WeightedVariants.succinctChoice`) |
| Bringmann and Panagiotou, "Efficient sampling methods for discrete distributions" (Algorithmica 2017) | `randomfunc`, weighted choice | Missing |
| Klundert, "Efficient generation of discrete random variates" (thesis, 2019), alias variant | `randomfunc`, weighted choice | Missing |
| Hübschle-Schneider and Sanders, "Parallel weighted random sampling", arXiv:1903.00227 (free) | `randomfunc`, weighted choice | Missing |
| Efraimidis and Spirakis, weighted sampling with keys, arXiv:1012.0256 (free, checked) | `randomfunc`, weighted sampling without replacement | Partly implemented (`Weighted.weightedReservoirOne`, `weightedWithoutReplacement`; the key-based scheme is missing) |
| Chao, "A general purpose unequal probability sampling plan" (Biometrika 1982) | `randomfunc`, weighted reservoir | Missing |
| Deville and Tillé, splitting method for unequal probability sampling (Biometrika 1998) | `randomfunc`, inclusion probabilities | Implemented (`Weighted.inclusionSplitting`) |
| Cohen and others, stream sampling for variance-optimal subset sums (SODA 2009) | `randomfunc`, inclusion probabilities | Missing |
| Farach-Colton and Tsai, "Exact sublinear binomial sampling" (Algorithmica 73, 2015) | `randomfunc`, binomial distribution | Implemented (`DiscreteExtra.binomialBinary`) |
| Bringmann and Friedrich, "Exact and efficient generation of geometric random variates and random graphs" (ICALP 2013) | `randomfunc`, `randmisc`, binomial and geometric | Implemented (`DiscreteExtra.binomialHalfRejection`) |
| Bringmann, Kuhn, and others, internal DLA (ICALP 2014) | `randomfunc`, `bernoulli`, binomial | Partly implemented (`DiscreteExtra.binomialHalfRejection`) |
| Gilbert, "Random graphs" (1959) | `randomfunc`, random graphs | Implemented (`randomGraph`) |
| Batagelj and Brandes, efficient generation of large random networks (2005), by geometric skipping | `randomfunc`, random graphs | Missing |
| Costantini, uniform spanning trees (thesis, 2020) | `randomfunc`, random graphs | Missing |
| Penschuck and others, "Recent advances in scalable network generation", arXiv:2003.00736 (free, checked) | `randomfunc`, random graphs | Missing |
| Lewis and Shedler, thinning for nonhomogeneous Poisson processes (1979) | `randomfunc`, Poisson processes | Missing |
| Marsaglia and Tsang, "A simple method for generating gamma variables" (2000) | `randomnotes`, gamma distribution | Partly implemented (`Numerical.gamma` is a grid algorithm) |
| Liu, Martin, and Syring, "Simulating from a gamma distribution with small shape parameter", arXiv:1302.1884 (from Occil's reference) | `randomnotes`, gamma distribution | Partly implemented (`Numerical.gammaSmallShape` is a grid algorithm) |
| Stuart, gamma-distributed products of independent random variables (1962) | `randomnotes`, gamma distribution | Missing |
| Box and Muller, and the Marsaglia polar method, for normal pairs | `randomnotes`, normal distribution | Partly implemented (`Numerical.normalBoxMuller`, `Numerical.normalPolar` are grid algorithms) |
| Micciancio and Walter, "Gaussian sampling over the integers: efficient, generic, constant-time" (CRYPTO 2017) | `randomnotes`, normal distribution | Missing |
| Kschischang, trapezoid-ziggurat Gaussian generator (2019) | `randomfunc`, normal distribution | Missing |
| Oberhoff, "Exact sampling and prefix distributions" (thesis, 2018), exact rejection with PSRNs | `exporand`, appendix | Partly implemented (`PSRN.newInsideShape`, `PSRN.newRejection`) |
| Li and El Gamal, universal coding scheme for remote generation | `exporand`, notes | Missing |
| Boehm, "Towards an API for the real numbers" (PLDI 2020) and constructive real interpretation (1987) | `randomfunc`, `exporand`, real numbers | Partly implemented (lazy reals in `PSRN`) |
| Pedersen, "Reconditioning your quantile function", arXiv:1704.07949 (free, checked) | `randomfunc`, `exporand`, inverse transform | Partly implemented (`General.inverseQuantile`) |
| Williamson, random points on curved surfaces (1987) | `exporand`, sphere and shapes | Partly implemented (`Multivariate.sphere`, `Multivariate.ellipsoidSurface`) |
| Banerjee and Sinha, generating an event with probability p^alpha (Sankhya 1979) | `bernoulli`, lambda^(x/y) | Implemented (`fractionalPower`) |
| Forsythe, von Neumann's comparison method for the normal and other distributions (1972) | `bernoulli`, series | Partly implemented (`expMinusFactory`) |
| Monahan, extensions of von Neumann's method (1979) | `bernoulli`, series | Partly implemented (`expMinusFactory`) |
| Leighton, proper continued fractions (1940); Gosper, continued fraction arithmetic (1978); Borwein and others, continued logarithms (2017) | `bernoulli`, continued fractions and logarithms | Implemented (`Constants.continuedFraction`, `Constants.continuedLogarithm`) |
| Penaud and Roques, Fibonacci words and the golden ratio coin (2002) | `bernoulli`, constants | Implemented (`Constants.goldenFamily`, `Constants.inverseGoldenRatio`) |
| Sondow, Vacca-type series for Euler's constant (2005) | `bernoulli`, constants | Implemented (`Constants.eulerMascheroni`) |
| Carvalho and Moreira, adaptive truncation of infinite sums (arXiv:2202.06121) | `bernoulli`, converging series | Partly implemented (`Constants.fromPositiveSeries`) |
| Szász, Bernstein polynomial operator on the infinite interval (1950) | `bernoulli`, notes | Missing |

## Most promising missing algorithms

The following list ranks the missing algorithms by two criteria: how exact the sampler is, and how many Occil articles depend on it. An exact sampler that needs only uniform bits and rational arithmetic ranks first. The count of articles comes from the citations I read.

1. **Dice enterprise and the general Bernoulli race (Morina and others, Schmon and others, Wästlund).** It is exact, uses only coin flips and rational polynomial coefficients, and appears in `bernoulli`, `bernsupp`, and `randextract`. The repository already has two-coin races, coupling from the past, and degree elevation of Bernstein coefficients, so most building blocks exist.
2. **Exact discrete Gaussian (Canonne, Kamath, and Steinke).** It needs only Bernoulli(exp(-x/y)) trials and geometric variates, and the repository has `expMinusRational` and `discreteLaplace` already. Two articles (`bernoulli`, `randmisc`) rely on it, and it matters for differential privacy work.
3. **Iterated von Neumann and optimal extractors (Peres, Pae, Zhou and Bruck, Camion, Pae and Loui).** These samplers are exact, use only bits, and appear in `randextract`, `bernoulli`, `bernsupp`, and `randmisc`. The repository has only the plain von Neumann extractor.
4. **Exponential variates from Bernoulli trials (Thomas and Luk, Flajolet and Saheb).** They are exact and need only bits. Two articles (`exporand`, `randomfunc`) cite them. The repository has the same law by other methods, so the gain lies in matching Occil's bit-level construction and its bit cost.
5. **Finite-state and pushdown generators and algebraic factories (Flajolet, Pelletier, and Soria; Mossel and Peres; Knuth and Yao).** They are exact and rational, and three articles (`bernoulli`, `bernsupp`, `randomfunc`) depend on them. The proofs need a grammar or automaton model, so the cost is higher than for items 1 to 4.
6. **Sum of two coins and the multivariate linear factory (Nacu and Peres, Huber).** Both are exact, small, and cited in `bernoulli`. They are quick additions next to `FactoryExtra.linear`.
7. **Poisson-variate form of the Bernstein-polynomial factory (Goyal and Sigman), and the Poisson count variants in `bernsupp`.** They are exact and small, but only one article depends on them.
8. **Random graphs by geometric skipping (Batagelj and Brandes) and MergeShuffle (Bacher and others).** They are exact given a geometric sampler and a uniform integer source, but `randomfunc` is the only article that cites them.
9. **Fill's interruptible algorithm and Huber's local-correctness method.** They are exact but need heavier Markov chain machinery, and few articles depend on them.
10. **Exact normal improvements (Du, Fan, and Wei; Micciancio and Walter).** They are exact but only speed up samplers that the repository already has.

Samplers that need real-number arithmetic, such as key-based weighted sampling without replacement (Efraimidis and Spirakis), Marsaglia-Tsang gamma, and ziggurat methods, rank last because they are approximate in floating-point form.
