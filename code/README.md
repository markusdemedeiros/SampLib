# Occil samplers as ProbLang terms

Import `Samplers` to use these algorithms. Each algorithm is an object-language `pl%` term
in the `Occil` namespace, generic over the representation of the reals. At `Float`, the
terms run in the interpreter. At `ℝ`, they are the targets of the continuous TotalEris
(CTE) proofs. No sampler calls a host implementation, the foreign function interface
(FFI), or an oracle for its target distribution. The only probabilistic primitives are
uniform integer and uniform real draws.

This set of implementations is broad, but it does not cover all of Occil's work.
Statistical interpreter tests cover it. The
[repository README](../README.md#formal-verification) lists the samplers that have formal
CTE correctness proofs.

## Module layout

Import `Samplers` to get the complete library, or import one family module:

| Module | Contents |
| --- | --- |
| `Samplers.Discrete.All` | Count laws, compound distributions, urns, and discrete tails |
| `Samplers.Combinatorial` | Collection sampling, shuffles, and permutations |
| `Samplers.Weighted.All` | Tables, probability trees, entropy recycling, and dynamic weights |
| `Samplers.Bernoulli` | Coin composition, linear and rational factories, series, and polynomials |
| `Samplers.Constants` | Digit and interval engines, and coins for named constants |
| `Samplers.Continuous` | Comparison-based ideal continuous samplers |
| `Samplers.Numeric` | Integer fixed-point arithmetic and elementary functions |
| `Samplers.Numerical.All` | Numerical scalar distributions, mixtures, and derived families |
| `Samplers.Multivariate` | Vector laws, copulas, geometry, and phase-type distributions |
| `Samplers.PSRN` | Partially sampled random numbers (PSRNs): lazy-real arithmetic, observations, and exact sampler constructions |
| `Samplers.General` | General schemes, point selection, and finite data models |

Large families split into smaller implementation files under these paths. The original
`More`, `Factories`, `FactoryExtra`, `DiscreteExtra`, `WeightedVariants`, and `Specialized`
modules still re-export their contents for compatibility. The `Occil` namespaces and
function signatures did not change.

## Conventions

The terms follow these conventions:

- An integer argument is an object-language integer. The names `n` and `k` do not
  denote Lean indices.
- A coin callback takes unit and returns a Boolean. A sampler callback takes unit and
  returns a value. Each fresh callback call must be independent and identically
  distributed, and independent of the auxiliary randomness of the sampler, including
  bag digits and selection coins.
- A list is `inl(unit)` when empty and `inr((head,tail))` otherwise. Pairs encode
  vectors of size two. Heap arrays appear only inside the shuffle and reservoir
  algorithms.
- `fail` signals rejected input. The domains in the table of techniques are preconditions, even where a term
  does not check every assumption. For example, no term checks the probability of an
  abstract coin.
- Geometric and negative-binomial counts are the failures before the required successes.
- Counts and weights use unbounded integers, not fixed-width machine arithmetic.

## Implemented techniques and domains

The following table gives the domain and intended result of each core routine, grouped by
module:

| Module and term | Domain and intended result |
| --- | --- |
| Uniform: `uniformInt` | n>0; uniform [0,n) |
| `rndInt`, `rndIntRange`, `rndIntExcRange` | Nonempty inclusive or exclusive integer intervals |
| `fastDiceRoller` | n>0; fair-bit Fast Dice Roller, uniform [0,n) |
| `uniformFromModulus` | modulus≥2,n>0; non-power-of-two rejection helper with recursive expansion |
| `fairCoin`, `rationalCoin` | Fair Boolean; exact p=x/y for 0≤x≤y,y>0 |
| `realCoin` | Ideal threshold Bernoulli(p), 0≤p≤1 |
| Discrete: `binomial` | n≥0; sum of n independent p-coin successes |
| `geometric`, `negativeBinomial` | p>0; failures before one or r≥0 successes |
| `dice` | count≥0,sides>0; sum of fair dice with faces 1..sides |
| `poissonOne`, `poissonRational` | Duchon-Duvignau Poisson(1), then additivity and thinning for Poisson(x/y), x≥0,y>0 |
| `weightedChoice` | Nonnegative integer weights with positive sum; category index |
| `multinomial` | n≥0; sequential conditional binomials for nonnegative weights, positive sum |
| `polyaEggenberger` | n≥0, initial counts nonnegative with positive sum, reinforcement≥0; successes in n draws |
| `hypergeometric` | n≤ones+zeros; nonnegative counts; successes without replacement |
| `randomWalk` | n≥0; sum of n independent symmetric unit steps |
| Combinatorial: `choice`, `sampleWithReplacement` | Nonempty input for each requested draw; arbitrary list items |
| `sampleWithoutReplacement` | 0≤k≤length; uniform ordered selection of distinct positions |
| `sampleInOrder` | Same domain; uniform k-subset in original input order |
| `shuffle` | Fisher-Yates over a temporary heap array; uniform permutation of positions |
| `reservoir` | 0≤k≤length; Algorithm R, uniform unordered subset; reservoir slot order is not promised uniform |
| `positiveComposition` | n>0,total≥n; uniform positive integer n-tuples summing to total |
| `weakComposition` | n>0,total≥0; uniform nonnegative compositions |
| `randomGraph` | n≥0; each possible undirected edge independently has callback probability p |
| Factories: `complement` | p -> 1-p |
| `coinProduct`, `coinDisjunction` | (p,q) -> pq and p+q-pq |
| `coinMean`, `coinConditional` | (p+q)/2 and rp+(1-r)q |
| `vonNeumann` | 0<p<1; fair coin from an unknown biased coin |
| `bernoulliRace` | p+q>0; p/(p+q) |
| `oneDivOnePlus` | 0≤p≤1; 1/(1+p), uniformly bounded expected iteration count |
| `evenParity` | 0≤p<1; 1/(1+p); diverges at p=1 |
| `fractionalPower` | 0<a≤b; p^(a/b), Mendo's factory; p=0 can have infinite expected cost |
| `expMinusRational` | x≥0,y>0; exp(-x/y), including integer-part factorization |
| `expMinusFactory` | exp(-p) from an abstract p-coin, by decreasing uniform trials and thinning |
| Continuous: `exponential` | Von Neumann unit-rate exponential, by decreasing-chain rejection |
| `laplace` | Laplace(0,1), independent exponential magnitude and sign |
| `erlang` | Positive integer shape, unit rate; independent exponential sum |
| `uniformSum` | n≥0; Irwin-Hall law, degenerate zero when n=0 |
| `uniformMin`, `uniformMax` | Minimum and maximum of two independent uniforms; Beta(1,2), Beta(2,1) |
| `orderStatistic` | 1≤k≤n; k-th order statistic, Beta(k,n+1-k) |
| `mixture` | Independent selector and abstract component samplers |
| `gaussian` | Standard normal, Karney-style comparison-based rejection |
| More: `boundedGeometric` | Truncated failure count; includes p=0 with a finite cap |
| `rejection` | Abstract proposal and acceptance callbacks; positive acceptance probability |
| `weightedRejection` | Uniform category proposals with a checked integer envelope |
| `weightedWithoutReplacement` | Sequential probability-proportional-to-weight ordered indices |
| `aliasSamples` | Exact integer Walker alias preprocessing in the heap; repeated draws |
| `sattolo` | Uniform single-cycle permutation, distinct from a uniform derangement |
| `derangement` | Uniform fixed-point-free permutation of positions, by rejection |
| `flipBits` | Independent callback-directed flips of a Boolean list |
| `logisticFactory` | cp/(1+cp), c a positive rational |
| `probabilityGeneratingFactory` | E[p^N] from an abstract nonnegative integer sampler |
| `bernsteinFactory` | Bernstein-polynomial factory with rational coefficients in [0,1] |
| Lazy: `newUniformBag`, `uniformBagStep`, `uniformBagPrefix` | Memoized binary uniform; persistent finite prefix observations |
| `uniformBagLess` | Exact comparison of a shared lazy uniform with an integer fraction |
| `sampleGeometricBag` | Conditional Bernoulli(U), with the same latent U preserved across calls |
| `factorialSeriesFactory`, `expMinusMartingale` | Exact integer-bound alternating-series exp(-p) construction |
| `cosineFactory`, `sineFactory` | cos(p), sin(p) from an abstract p-coin |
| `logOnePlusFactory` | ln(1+p) from a p-coin and a shared uniform bag |
| `arctanOverPFactory`, `arctanFactory` | arctan(p)/p (value 1 at p=0), arctan(p) |

`Data` contains list operations. The helpers `fillArray` and `readArray`, the
decreasing-trial and iteration routines, the exponential-half coin, and the Gaussian
selectors are supporting `pl%` routines. The Gaussian implementation expands the Karney
construction instead of calling the upstream `Gauss` or the named Gaussian primitive. Its
structure follows the upstream `Metrology/Code/Samplers.lean`, whose CTE examples can
guide proofs.

Every Bernstein coefficient needs a positive denominator and a numerator between zero and
that denominator. The routine checks only the coefficient that it selects.

Lazy rational comparisons are exact almost surely under the uniform-bit law. Dyadic
numbers with two representations and tails of all ones form null exceptions, so the
comparison is not correct for every adversarial infinite bit stream. Repeated geometric
bag calls share U on purpose. Their unconditional pair law is therefore correlated, and a
separate test covers it, apart from independent coin products.

## Source correspondence and explicit adaptations

The translation draws on these articles by Peter Occil:

- [Randomization and Sampling Methods](https://peteroupc.github.io/randomfunc.html)
- [More Random Sampling Methods](https://peteroupc.github.io/randomnotes.html)
- [Bernoulli Factory Algorithms](https://peteroupc.github.io/bernoulli.html) and linked `bernoulli.py`
- [A Note on Randomness Extraction](https://peteroupc.github.io/randextract.html)

The code translates the algorithms. It does not transcribe every line of pseudocode,
and it deviates from the articles on purpose in these ways:

1. Fisher-Yates uses the selected `j` in both swaps. The article prints `k` there.
2. Ordered subset sampling tests `u < needed`, not `u <= needed`, for u uniform in
   [0,remaining). The second test selects too often and can return too few items.
3. Pólya urn draws use `ones/(ones+zeros)`. The printed `ZeroOrOne(ones,zeros)` does not
   match the stated interface of a numerator and a denominator. This implementation
   supports nonnegative reinforcement, and `hypergeometric` handles negative
   reinforcement.
4. The multinomial sampler renormalizes with the sums of the remaining integer weights.
   It replaces the inconsistent name `t` in the article with the current count of
   remaining trials.
5. `binomial` sums trials directly, as the definition of the distribution describes. It
   is not the optimized bit-decomposition implementation that the article prints as
   `BinomialInt`.
6. Compositions choose uniform ordered subsets as cut points, instead of rejecting
   duplicate cut points. The cut points have the same intended distribution.
7. `randomGraph` uses the independent-edge construction, not the geometric skip variant.
8. `expMinusFactory` uses decreasing uniforms that the input coin thins. The chance of
   surviving n iterations is p^n/n!, so stopping at an even count gives exp(-p). This
   comparison-based variant of alternating-series sampling does not transcribe the
   cached uniform and martingale implementation of the Python routine.
9. The Erlang, Laplace, minimum, maximum, sum, and mixture samplers compose the basic
   techniques. Separate test cases exercise each composed output law.
10. All samplers use the ideal independence assumptions of ProbLang. The interpreter
    substitutes a seeded pseudorandom number generator and finite-precision IEEE operations.
11. `linearLowProbability` passes the margin `1/2` to its inner linear factory. Its stated
    bound `μ ≤ ρ < 1/2` ensures `μ/(2ρ) ≤ 1/2`. The previous margin, `1−ρ`, required the
    stronger bound `μ ≤ 2ρ²`. The
    [repair review](../agent-docs/reviews/ExactLowProbabilitySourceRepair001.md) records
    the exact one-line change and the CTE argument for the full domain. The
    [runtime regression](../agent-docs/reviews/LowProbabilityRuntime001.json) covers
    expanding, contracting, zero, and invalid inputs on both interpreters.
12. `optimalMatrix` encodes a row with probability one by setting all `k` bits, which
    represents the cyclic expansion `0.111… = 1`. The previous encoding could overflow the
    scanned width, so that some distributions, such as `[2, 0]`, looped forever. The
    [independent repair review](../agent-docs/reviews/ExactOptimalSourceRepair001.md)
    records the exact change and the argument about row masses. The
    [interpreter regression](../agent-docs/reviews/OptimalRepairRuntime002.json) passes 88
    exact matrix checks and 528 runs of the draw and its wrappers. These runs cover every
    certain position in lists of up to five items, plus nondegenerate controls. The other
    row encodings and the traversal algorithm did not change.

The file `agent-docs/OccilSources.json` fingerprints the documents that the translation
used. The live pseudocode on the website might change.

## Coverage and remaining work

The [repository index](../README.md) lists Occil's sampling techniques and links to
their implementations. The table of techniques and domains introduces the core routines. The family modules
also contain the later numerical, multivariate, weighted, and PSRN additions. The
[wishlist](../agent-docs/ProbLangWishlist.md) records what the language, the
interpreter, and the proof library still need.
