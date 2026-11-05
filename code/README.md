# Occil samplers as ProbLang terms

Import `Samplers`. All algorithms are object-language `pl%` terms in namespace
`Occil`, generic over the real representation. Instantiating them at `Float` runs
them in the interpreter; instantiating them at `ℝ` gives future CTE proof targets.
No sampler calls a host implementation, FFI, or an oracle for its target distribution.
Uniform integer/real draws are the only probabilistic primitives used.

This is a broad initial implementation set, not complete coverage of Occil's corpus.
It has statistical interpreter tests, not formal correctness proofs yet.

## Conventions

- An integer argument is an object-language integer; `n` and `k` are not Lean indices.
- A coin callback takes unit and returns a Boolean; a sampler callback takes unit and
  returns a value. Fresh callback calls must be iid and independent of the sampler's
  auxiliary randomness, including bag digits and selection coins.
- Lists are `inl(unit)` for nil and `inr((head,tail))` for cons. Pairs encode vectors
  of size two; heap arrays are internal to shuffle and reservoir algorithms.
- `fail` signals rejected input. Domains below are preconditions even where a term
  does not check every assumption (notably abstract-coin probabilities).
- Geometric and negative-binomial counts mean failures before the required successes.
- Counts and weights use unbounded integers, not fixed-width machine arithmetic.

## Implemented techniques and domains

| Module / term | Domain and intended result |
| --- | --- |
| Uniform / `uniformInt` | n>0; uniform [0,n) |
| `rndInt`, `rndIntRange`, `rndIntExcRange` | Nonempty inclusive/exclusive integer intervals |
| `fastDiceRoller` | n>0; fair-bit Fast Dice Roller, uniform [0,n) |
| `uniformFromModulus` | modulus>=2,n>0; non-power-of-two rejection helper with recursive expansion |
| `fairCoin`, `rationalCoin` | Fair Boolean; exact p=x/y for 0<=x<=y,y>0 |
| `realCoin` | Ideal threshold Bernoulli(p), 0<=p<=1 |
| Discrete / `binomial` | n>=0; sum of n independent p-coin successes |
| `geometric`, `negativeBinomial` | p>0; failures before one or r>=0 successes |
| `dice` | count>=0,sides>0; sum of fair dice with faces 1..sides |
| `poissonOne`, `poissonRational` | Duchon–Duvignau Poisson(1), then additivity/thinning for Poisson(x/y), x>=0,y>0 |
| `weightedChoice` | Nonnegative integer weights with positive sum; category index |
| `multinomial` | n>=0; sequential conditional binomials for nonnegative weights, positive sum |
| `polyaEggenberger` | n>=0, initial counts nonnegative with positive sum, reinforcement>=0; successes in n draws |
| `hypergeometric` | n<=ones+zeros; nonnegative counts; successes without replacement |
| `randomWalk` | n>=0; sum of n independent symmetric unit steps |
| Combinatorial / `choice`, `sampleWithReplacement` | Nonempty input for each requested draw; arbitrary list items |
| `sampleWithoutReplacement` | 0<=k<=length; uniform ordered selection of distinct positions |
| `sampleInOrder` | Same domain; uniform k-subset in original input order |
| `shuffle` | Fisher–Yates over a temporary heap array; uniform permutation of positions |
| `reservoir` | 0<=k<=length; Algorithm R, uniform unordered subset; reservoir slot order is not promised uniform |
| `positiveComposition` | n>0,total>=n; uniform positive integer n-tuples summing to total |
| `weakComposition` | n>0,total>=0; uniform nonnegative compositions |
| `randomGraph` | n>=0; each possible undirected edge independently has callback probability p |
| Factories / `complement` | p -> 1-p |
| `coinProduct`, `coinDisjunction` | (p,q) -> pq and p+q-pq |
| `coinMean`, `coinConditional` | (p+q)/2 and rp+(1-r)q |
| `vonNeumann` | 0<p<1; fair coin from an unknown biased coin |
| `bernoulliRace` | p+q>0; p/(p+q) |
| `oneDivOnePlus` | 0<=p<=1; 1/(1+p), uniformly bounded expected iteration count |
| `evenParity` | 0<=p<1; 1/(1+p); diverges at p=1 |
| `fractionalPower` | 0<a<=b; p^(a/b), Mendo's factory; p=0 can have infinite expected cost |
| `expMinusRational` | x>=0,y>0; exp(-x/y), including integer-part factorization |
| `expMinusFactory` | exp(-p) from an abstract p-coin, via decreasing uniform trials and thinning |
| Continuous / `exponential` | Von Neumann unit-rate exponential, via decreasing-chain rejection |
| `laplace` | Laplace(0,1), independent exponential magnitude and sign |
| `erlang` | Positive integer shape, unit rate; independent exponential sum |
| `uniformSum` | n>=0; Irwin–Hall law, degenerate zero when n=0 |
| `uniformMin`, `uniformMax` | Min/max of two independent uniforms; Beta(1,2), Beta(2,1) |
| `orderStatistic` | 1<=k<=n; k-th order statistic, Beta(k,n+1-k) |
| `mixture` | Independent selector and abstract component samplers |
| `gaussian` | Standard normal, Karney-style comparison-based rejection |
| More / `boundedGeometric` | Truncated failure count; includes p=0 with a finite cap |
| `rejection` | Abstract proposal and acceptance callbacks; positive acceptance probability |
| `weightedRejection` | Uniform category proposals with a checked integer envelope |
| `weightedWithoutReplacement` | Sequential probability-proportional-to-weight ordered indices |
| `aliasSamples` | Exact integer Walker alias preprocessing in the heap; repeated draws |
| `sattolo` | Uniform single-cycle permutation, distinct from a uniform derangement |
| `derangement` | Uniform fixed-point-free permutation of positions, via rejection |
| `flipBits` | Independent callback-directed flips of a Boolean list |
| `logisticFactory` | cp/(1+cp), c a positive rational |
| `probabilityGeneratingFactory` | E[p^N] from an abstract nonnegative integer sampler |
| `bernsteinFactory` | Bernstein-polynomial factory with rational coefficients in [0,1] |
| Lazy / `newUniformBag`, `uniformBagStep`, `uniformBagPrefix` | Memoized binary uniform; persistent finite prefix observations |
| `uniformBagLess` | Exact comparison of a shared lazy uniform with an integer fraction |
| `sampleGeometricBag` | Conditional Bernoulli(U), with the same latent U preserved across calls |
| `factorialSeriesFactory`, `expMinusMartingale` | Exact integer-bound alternating-series exp(-p) construction |
| `cosineFactory`, `sineFactory` | cos(p), sin(p) from an abstract p-coin |
| `logOnePlusFactory` | ln(1+p) from a p-coin and a shared uniform bag |
| `arctanOverPFactory`, `arctanFactory` | arctan(p)/p (value 1 at p=0), arctan(p) |

`Data` contains list operations; `fillArray`, `readArray`, decreasing-trial,
iteration, exponential-half coin and Gaussian selectors are supporting pl% routines.
The Gaussian implementation expands the Karney construction rather than calling
upstream `Gauss` or the named Gaussian primitive. Its structure follows upstream
`Metrology/Code/Samplers.lean`, where corresponding CTE examples can guide proofs.

Every Bernstein coefficient must have a positive denominator and numerator between
zero and that denominator; the routine checks only the selected coefficient.
Lazy rational comparisons are exact almost surely under the uniform-bit law.
Dyadic dual representations and all-ones tails are null exceptions, so the comparison
is not claimed correct for every adversarial infinite bit stream. Repeated geometric
bag calls intentionally share U; their unconditional pair law is correlated and is
tested separately from independent coin products.

## Source correspondence and explicit adaptations

Primary sources:

- [Randomization and Sampling Methods](https://peteroupc.github.io/randomfunc.html)
- [More Random Sampling Methods](https://peteroupc.github.io/randomnotes.html)
- [Bernoulli Factory Algorithms](https://peteroupc.github.io/bernoulli.html) and linked `bernoulli.py`
- [A Note on Randomness Extraction](https://peteroupc.github.io/randextract.html)

This is an algorithmic translation, not a literal transcription of every pseudocode
line. The following deviations are deliberate:

1. Fisher–Yates uses the selected `j` in both swaps; the article prints `k` there.
2. Ordered subset sampling tests `u < needed`, not `u <= needed`, for u uniform in
   [0,remaining). The latter selects too frequently and can return too few items.
3. Pólya urn draws use `ones/(ones+zeros)`; the printed `ZeroOrOne(ones,zeros)`
   does not match the stated numerator/denominator interface. Nonnegative reinforcement
   is supported here; negative reinforcement is handled separately by `hypergeometric`.
4. Multinomial uses remaining integer weight sums for conditional renormalization;
   the article's inconsistent `t` name is replaced with the current remaining trial count.
5. `binomial` is the direct trial-sum construction described by the distribution;
   it is not the optimized bit-decomposition implementation printed as `BinomialInt`.
6. Compositions use uniform ordered subset cut points rather than rejection of
   duplicate cut points. The cut-point distribution is the same intended one.
7. `randomGraph` is the independent-edge construction, not the geometric skip variant.
8. `expMinusFactory` uses decreasing uniforms thinned by the input coin. Survival
   through n iterations has probability p^n/n!, so even stopping parity gives exp(-p).
   This is a comparison-based variant of alternating-series sampling; it is not a
   transcription of the Python routine's cached uniform/martingale implementation.
9. Erlang, Laplace, min/max, sum and mixture constructions are compositions of the
   basic techniques. Their separate test cases exercise the composed output laws.
10. All samplers use the ideal independence assumptions of ProbLang. The executable
    interpreter substitutes a seeded PRNG and finite-precision IEEE operations.

The source fingerprint file in `agent-docs/OccilSources.json` identifies the documents
consulted; no claim is made that the website's live pseudocode will stay unchanged.

## Deferred coverage

Fast loaded-dice/tree optimizations, general rational/real-weight samplers, general gamma/beta,
Box–Muller/polar normal, arbitrary affine scaling, stable/von Mises, multivariate and
geometric samplers, general PSRN arithmetic and general function-envelope factories are
not implemented here. See [the consolidated wishlist](../agent-docs/ProbLangWishlist.md)
for the language, interpreter and proof-library capabilities they need.
