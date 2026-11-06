# Expansion: structured sampler review

Reviewer: `expand_review_structured`.

This review covers general sampling schemes, combinatorial samplers, point sets,
heap-backed sampling, exact continuous samplers, and finite-state kernels.
Only the accepted entries below have completed independent checks. Mathematical
helpers and selectors are supporting infrastructure rather than extra samplers.

The persistent caller suite is `ExpansionStructuredCallers.lean`. Each accepted
entry requires source review, a warning-free independent build, standard-axiom
checks, a resource-framed public caller, and relevant boundary/infinite-credit
checks. Exact source and transitive-import snapshots are retained in the receipt.

## Accepted samplers

Batch001 contains five independently accepted samplers. Its immutable caller is
`ExpansionStructuredBatch001Callers.lean`; its receipt is
`ExpansionStructuredBatch001.json`. All independent target builds and callers
completed without warnings. Inspected public specs and central expectation lemmas
use only `propext`, `Classical.choice`, and `Quot.sound`.

The new `SupportedSpec.wp_supported` helper was independently reviewed and built:
a measurable if-kernel assigns infinity off the almost-sure support, its integral
is unchanged a.e., and invalid infinite credit excludes impossible outputs while
retaining a caller resource. `ListProduct` supplies normalized independent-list
laws and the countable Fubini identity. Neither helper is counted as a sampler.

### `Occil.General.generativeModel`

Accepted `SampLib.GenerativeModel.generativeModel_distSpec`, SHA-256
`cb42ff7d841e8a09d404efa7ff4eabb3d6acf98a0855616117ae90c723a27c10`.

Domain: Any probability law on a measurable latent space and any measurable decoder with its deterministic callback contract.

Change of variables identifies the independent latent-law pushforward. The CTE proof calls the latent sampler and then the decoder. Framed callers and degenerate Bernoulli decoder tests include infinity on null and actual outputs.

### `Occil.General.inverseQuantile`

Accepted `SampLib.InverseQuantile.inverseQuantile_distSpec`, SHA-256
`94482c760a6f73e6c1ee3a7518f20c5e89efbccfb1e50129089f1022bf2f98b3`.

Domain: Every integer scale>1, represented as n+1 with n>0; supplied quantiles on interior ranks1..n.

Uniform interior ranks are pushed through the supplied quantile. The callback arguments match the actual scale and rank. Tests cover scale2, noninjective constant quantiles, infinity outside support, and framing.

### `Occil.General.kernelDensity`

Accepted `SampLib.KernelDensity.kernelDensity_distSpec`, SHA-256
`2a2a1ae2971381e2d3c1e35e87289c5592963bfe798aad1721c7781875e0ddb5`.

Domain: Every nonempty integer observation list and every normalized integer jitter law, including duplicates and unbounded supports.

An independent empirical position and kernel offset give the convolution expectation. Tests check duplicate-center mass2/3, translated deterministic centers, null-event infinity, all-infinite credits, and framing.

### `Occil.General.uniformBoxPoint`

Accepted `SampLib.UniformBoxPoint.uniformBoxPoint_distSpec`, SHA-256
`1bf413cb67405d45e36f429abcb22f1f3e15aea976c4496c2e80a5bce488ecca`.

Domain: Every positive natural grid scale and every natural dimension, including dimension0.

The product-list Fubini identity supplies independent coordinates uniform in[0,scale). The CTE proof is a finite induction. Tests cover empty points, scale1 deterministic coordinates, infinity off support, and framing.

### `Occil.flipBits`

Accepted `SampLib.FlipBits.flipBits_distSpec`, SHA-256
`cc8466c02431dc08574a7b35840dff26feef0cf188389d3646abc760dd7a5432`.

Domain: Every Boolean input list and bias in[0,1], including empty lists and deterministic endpoint coins.

The full ordered output law is the independent Bernoulli-toggle product. Tests identify endpoint laws as the input or complemented list, include empty input and infinite credits, and frame arbitrary caller resources.


## Batch002

Eight samplers accepted, including two explicitly classified derived named wrappers.
The immutable caller is `ExpansionStructuredBatch002Callers.lean`; the receipt is
`ExpansionStructuredBatch002.json`. All independent target builds and the full
caller suite pass without warnings. Every inspected public/central theorem uses
only the standard three axioms.

Supporting stochastic-list-map and syntax lemmas were independently reviewed.
The Gaussian bridge only publicly imports existing upstream mathematics.
GaussianSelector is support, not an extra counted sampler: the actual thinned
chain uses a uniform stopping gap, even at x=1, giving the fixed amplification
factor(2k+2)/(2k+1). Its expectation inequality is ENNReal-safe; k=0/x=0/x=1
boundary formulas and standard-axiom checks pass. No selector/helper is counted.

### `Occil.General.stoppedSum`

Accepted `SampLib.StoppedSum.stoppedSum_distSpec`, SHA-256
`8aaf5d5f4caa32f52931ce4fa9d23a56c863d2defdedf90f1801996a3f3115a2`.

Domain: Any normalized natural stopping-count law and normalized integer summand law; no moment assumptions, including zero counts.

The canonical random-sum law mixes independent finite convolutions against the count law. The CTE proof samples one count and executes its finite loop. Independent tests include zero stopping counts, arbitrary count laws with constant summands, infinity, and framing.

### `Occil.General.episodes`

Accepted `SampLib.Episodes.episodes_distSpec`, SHA-256
`198624fb20d5d4660552c972c1eafb63e5b608a8081efbccadeafa70809f270e`.

Domain: Any normalized natural count law and normalized integer summand law, with the same sampled count retained in the returned pair.

The joint law pairs each conditional finite sum with its count. An arbitrary-count test with constant1 summands assigns infinity off sum=count and verifies expectation7, checking the required correlation. Framed callers and zero-count behavior pass.

### `Occil.General.kernelDensityVector`

Accepted `SampLib.KernelDensityVector.kernelDensityVector_distSpec`, SHA-256
`4528202cdf004ab69885d29a0e1f9cd057c4977fe2d2ec3dfd03b79de488f7d4`.

Domain: Any nonempty list of finite integer vectors and any normalized scalar jitter law; empty or differing vector lengths are permitted.

One empirical center is sampled before independent coordinate jitters. The ListMapSampling support gives the full joint law. A zero-jitter test excludes spurious mixed coordinates from centers[0,10] and[10,0], with infinity off support; empty vectors and framed callers pass.

### `Occil.General.stratified1D`

Accepted `SampLib.Stratified1D.stratified1D_distSpec`, SHA-256
`064901e7d741707e26e16e37e8395a8cfb5b07b2b7c8a21e6d48ab0bac3cdb4d`.

Domain: Positive strata count at most the positive integer grid scale; bins use exactly floored boundaries.

Rounded-bin nonemptiness is established mathematically, and product-list Fubini supplies independent stratum draws. The CTE proof uses named guard/index facts. Tests cover unequal rounded widths, one stratum, unit-width strata, infinity, and framing.

### `Occil.General.randomString`

Accepted `SampLib.RandomString.randomString_distSpec`, SHA-256
`46da282f750a39d2201bd32ad3ebbb5c258f34370c231483216b8d0d22b64a1d`.

Domain: Any natural length over a nonempty alphabet; a separate zero-length spec covers every alphabet, including empty, without a uniform-integer assumption.

This is the actual named wrapper around verified replacement sampling. Position multiplicity is preserved; an explicit duplicate-alphabet test checks probability2/3. The zero-length caller requires no randomness class and retains arbitrary framed resources.

### `Occil.General.randomDateTime`

Accepted `SampLib.RandomDateTime.randomDateTime_distSpec`, SHA-256
`ab432d6a09b2140f5c7fb8db0e710c7d3a59ca741398901092c62bc038dad24e`.

Domain: Every nonempty inclusive signed integer timestamp interval, including negative and singleton intervals.

The wrapper delegates to the verified inclusive integer-range law after closedness normalization. The framed public caller and a negative singleton interval with infinity away from its timestamp both pass.

### `Occil.expHalfCoin`

Accepted `SampLib.ExpHalfCoin.expHalfCoin_distSpec`, SHA-256
`869001e4dbfaf82c7a4b750d17ac37efc5635742002dac7721caecd1d9c21b9d`.

Domain: No parameters; exact Bernoulli bias exp(-1/2) over mathematical reals.

The lower half of the uniform interval uses decreasing-chain parity; the upper half returns true. Existing factorial/parity analysis identifies exp(-1/2). Private integer-parity normalization makes the main proof return the parity directly. Bias/success-mass, infinite-credit, and framed checks pass.

### `Occil.gaussianInteger`

Accepted `SampLib.GaussianInteger.gaussianInteger_distSpec`, SHA-256
`925bfe8e1bbf9d4369077e17b1bce9fa12cf1a679113dab5ebad133977ee25d9`.

Domain: No parameters; normalized nonnegative integer masses proportional to exp(-k²/2).

The geometric proposal and repeated exp(-1/2) coin acceptance collapse to the standard Gaussian integer mass. Actual Occil geometric/iteration combinators are definitionally identified with verified upstream generic combinators. Probability algebra is outside the adapter proof. Zero-atom, normalization/infinity, and framed checks pass.

## Batch003

Four further samplers accepted, with immutable caller
`ExpansionStructuredBatch003Callers.lean` and receipt
`ExpansionStructuredBatch003.json`. Independent target builds, framed callers,
boundary/duplicate/infinite-credit checks, formatting and standard-axiom checks
all pass without warnings.

The measurable-output transport helper preserves encodings and caller resources.
New closedness/support bridges are pure facts; GeneralSyntax reuses the shared
integer-range facts instead of duplicating them. The sorting bridge only imports
mathlib's list-sort API.

ArrayOwnership supplies an ordinary separation-logic array lens and load/store,
fill/read rules, preserving the complete array. Its framed read client and
vector adapters compile; uniform-integer assumptions on heap operations come
from the current upstream rule signatures. Permutations supplies the canonical
last-image/smaller-permutation bijection, reciprocal-factorial masses, and the
finite-uniform expectation, valid for arbitrary ENNReal credits. Independent
empty/singleton/infinite-credit and same-index swap tests pass. None of these
supporting helpers is an additional sampler.

### `Occil.gaussian`

Accepted `SampLib.Gaussian.gaussian_distSpec`, SHA-256
`d2560c0311bcf04cfd1d6584b3b1bc8c84f58fb19663a9739a43a832073c13cf`.

Domain: Exact standard Gaussian over mathematical reals, with the actual integer-bit fair sign primitive.

The standard gaussianReal(0,1) law is identified through upstream half-normal strip analysis. Own symbolic execution proves the actual Gaussian integer, selector acceptance loop, and integer-bit sign composition. No adequacy or Float rounding claim is added. Arbitrary measurable framed credits and all-infinite credit checks pass.

### `Occil.orderStatistic`

Accepted `SampLib.OrderStatistic.orderStatistic_distSpec`, SHA-256
`acae4ac5f14438cc108b17d51d13a5d58cd346bea9ce2234a80298f908897575`.

Domain: Every rank1≤k≤n, using a normalized iid uniform real vector and the canonical kth-sorted-value encoder; ties retain multiplicity.

Tonelli supplies the expectation identity for the iid vector. The deterministic sort is independently characterized as the unique ascending permutation of the original sample; the rank encoder is in bounds. The CTE proof performs uniform draws, pure insertions, and the final lookup. Tests cover n1, repeated equal values, maximum rank, arbitrary measurable framing, and infinity. No unproved Beta-density/CDF identification is claimed.

### `Occil.General.bootstrap`

Accepted `SampLib.Bootstrap.bootstrap_distSpec`, SHA-256
`956a30712df053fc85d584f3a33b583d16e5be5989e54520039da68777abf44d`.

Domain: Every finite empirical data set and natural replicate count; an empty-data spec needs no uniform-integer class.

The target is the nested independent empirical-position product, preserving duplicate observations. The program uses verified replacement sampling inside independent repetition. Public callers exercise arbitrary credits/resources, zero replicates, all-infinite credits, and every empty-data replicate count without a randomness assumption.

### `Occil.General.histogram`

Accepted `SampLib.Histogram.histogram_distSpec`, SHA-256
`6d558841f4bf0ebae7d8d346be9159078fca550f54c7e14279e365227cb56aaf`.

Domain: Nonnegative integer bin counts of positive total, one more boundary than counts, and strictly positive integer bin widths; zero counts are permitted.

The mathematical law mixes uniform bins by their count masses. Supported categorical sampling supplies valid indices; remaining program steps are deterministic lookups and a verified integer-range draw. Unequal-width bins have equal mass under equal counts, and infinity on a zero-count bin contributes zero. Framed and signed-grid callers pass.

## Batch004

Six samplers accepted with immutable Batch004 caller and receipt. Independent
builds and framed callers pass warning-free; boundary, duplicate, zero-mass
infinite-credit and standard-axiom checks pass. Composition laws use the existing
cut-sampler discrete measurable-list convention; caller sections make it explicit.

The support math gives the complete cut-gap bijection and stars-and-bars laws,
plus the Cartesian cell product. ArrayPermutation factors the ordinary separation
of a finalized last cell and remaining prefix. Closedness/list/integer-power
helpers are deterministic. SamplerStep constructs exactly the existing checked
pure-context rule, leaving the symbolic reduct available for caller normalization;
it introduces no new logical rule or axiom. These helpers add no sampler count.

### `Occil.shuffle`

Accepted `SampLib.Shuffle.shuffle_distSpec`, SHA-256
`0f4514cd7f7c1bdcf6a650a2783f4deda691bb0624e08a2724e967390ac90517`.

Domain: Every finite list, including empty lists and duplicate values, with arbitrary value encoders.

The target is the independent uniform position-permutation law. Fisher–Yates follows the last-image/smaller-permutation bijection; the separation-logic proof allocates, fills, swaps, recursively shuffles, and reads the complete array. Indexed ownership handles self-swaps and preserves caller resources. Independent empty/duplicate callers and standard-axiom checks pass.

### `Occil.positiveComposition`

Accepted `SampLib.PositiveComposition.positiveComposition_distSpec`, SHA-256
`5058435a1843ae05e0993aa1a6499941e83a296e03020d301c32d2614d22d016`.

Domain: Every positive part count n and total≥n.

Increasing interior cuts and consecutive gaps are proved inverse, giving exactly all ordered positive compositions, each with reciprocal binomial mass. The CTE proof composes the deterministic integer interval, uniform cut subset, and pure gap constructor. Independent singleton-count, valid reciprocal-sixth atom, impossible zero part, infinity and framed tests pass.

### `Occil.weakComposition`

Accepted `SampLib.WeakComposition.weakComposition_distSpec`, SHA-256
`a5180317a23214d8a172e2cced2adb271063a8b7405481d8401048f9664392f1`.

Domain: Every positive part count n and every natural total, including zero.

Adding or subtracting one per coordinate bijects weak and positive compositions, yielding the exact stars-and-bars singleton law. The program uses the positive sampler followed by deterministic subtraction. Independent zero-total and reciprocal-sixth atoms, full arbitrary-credit framing, and infinity tests pass.

### `Occil.General.latinHypercube1D`

Accepted `SampLib.LatinHypercube1D.latinHypercube1D_distSpec`, SHA-256
`54b652a2f69aef90683c77c8cb00c061feb370c6379f1ccf0116a41b10bda78d`.

Domain: Every integer grid with 1≤strata≤scale.

The canonical law jitters independently within rounded integer strata, then applies an independent uniform positional permutation. Conditioning on the jittered vector is the sole expectation identity. The program composes exactly those two verified samplers. Unequal-width strata are explicitly not claimed to give uniform whole-grid marginals. Singleton-grid, infinity and generic framed callers pass.

### `Occil.General.stratifiedBox`

Accepted `SampLib.StratifiedBox.stratifiedBox_distSpec`, SHA-256
`d0a8dfb44a2a314857333679cc58352f71e60c7949cd9cfb9ba8c8a1cebcb91b`.

Domain: Positive grid dimension,1≤bins≤scale, and every natural per-cell draw count including zero.

The target is an independent product of per-cell jitter chunks, flattened in increasing cell order. Base-bins digits select the correct coordinate strata. The mathematical continuation identity is product Fubini followed by concatenation; the program performs integer power, recursion, independent repeated cell calls and deterministic append. Zero repetitions are independently proved to return an empty law for all cells and dimensions; framing and infinity pass.

### `Occil.General.classifiedModel`

Accepted `SampLib.ClassifiedModel.classifiedModel_distSpec`, SHA-256
`e7a08d296095f9d345a663f764751113ad1297e567c695c3b3ac553a467e721f`.

Domain: Nonnegative integer class weights of positive sum and a matching finite family of normalized specified class-conditional callbacks; zero class weights are allowed.

The law retains the selected class tag and its conditional observation, preserving their correlation on an arbitrary measurable observation type. Supported categorical sampling removes out-of-range indices before pure lookup and the selected callback. Independent zero-weight examples show infinite credit on an impossible class costs zero; the positive class observation remains correctly tagged. Generic measurable credits and framed resources pass.

## Batch005

Five samplers accepted, with immutable Batch005 callers and receipt. Sequential
independent target builds, source review, arbitrary-credit framing, boundaries,
infinity and standard-axiom checks all pass without warnings.

FiniteKernels formalizes normalized countable-state finite iterates, trajectories,
and coordinate sweeps, with finite detailed-balance invariance. The stochastic
matrix adapter only totalizes row lookup outside its proved reachable support.
SattoloLaw proves full-orbit insertion/removal, factorial cardinality, exact
uniform masses and expectation, with explicit empty/singleton conventions.
BindFrom structurally finds the focus from an instantiated known theorem and
constructs the existing checked TWP evaluation-context rule. Its consumer proofs
are kernel-checked with exactly the three standard axioms. None of these
supporting modules adds a sampler count.

### `Occil.General.markovChain`

Accepted `SampLib.MarkovChain.markovChain_distSpec`, SHA-256
`325114027310e598ac3353f76dd5d3abd357f3c3e135e01b1ec9e2b197a74b89`.

Domain: Every square nonnegative integer-weight transition matrix with positive row totals, valid initial state and finite natural step count; the separate zero-step spec accepts arbitrary matrix and initial values without uniform randomness.

The target is the finite iterate of the normalized stochastic kernel. Its support remains inside the finite state space. CTE follows one row lookup/category call then the induction hypothesis, using supported callbacks. The generic zero-step caller preserves any initial Val and resource without uniform-integer assumptions; alternating-matrix, infinity, and framed callers pass.

### `Occil.General.randomMap`

Accepted `SampLib.RandomMap.randomMap_distSpec`, SHA-256
`ad246faf6c0f3f6e0abedde83e0c60e525b434a18a90bcd62cb25fbebda62d5a`.

Domain: Every finite list of positive-total nonnegative integer rows, including no rows; row lengths need not be equal.

The mathematical law independently chooses one categorical destination per row. Its product-Fubini identity is independent of program syntax. Program recursion samples the tail then the current row, retaining exact row order. Empty-matrix and deterministic alternating-row laws, arbitrary framed credits, infinity and standard axioms pass. The BindFrom tactic only applies the existing checked evaluation-context rule.

### `Occil.General.randomWalkPath`

Accepted `SampLib.RandomWalkPath.randomWalkPath_distSpec`, SHA-256
`ba9d7ec6065201c56b3db93b40a538d2fcb014c0e5511592a84f0af6dd2c76e4`.

Domain: Every normalized integer increment callback, signed integer start and natural step count.

The law scans an independent increment vector by addition, retaining the initial position. Fubini and scanl_cons give the sole expectation identity. The program samples an increment and recursively constructs the remaining path. Independent zero steps and three negative increments from a positive start demonstrate path length, initial-state convention and signed arithmetic; framed arbitrary credits and infinity pass.

### `Occil.sattolo`

Accepted `SampLib.Sattolo.sattolo_distSpec`, SHA-256
`c6c14ee66401d97d278cfcf989c0e2fa75e9510806ffa2db736cbc974fd2d9e0`.

Domain: Every finite list and arbitrary value encoder, including empty, singleton and duplicate-valued lists.

The normalized target is uniform over full position cycles, with explicit empty/singleton identity conventions. Insertion into an old orbit is bijective with a new full cycle, yielding factorial cardinality and expectation. The CTE proof uses strict earlier-position choices and the checked shared array swap ownership invariant. Independent cardinality24, reciprocal-sixth masses, identity exclusion at size3, duplicate/empty decoders, infinity and framed callers pass.

### `Occil.General.permutationSamples`

Accepted `SampLib.PermutationSamples.permutationSamples_distSpec`, SHA-256
`53464b5e71f22c0727df6396129c076d3c3dd59093ccaf6819be929c8bab960e`.

Domain: Every finite observation list and natural replicate count, including empty observations, duplicate values and zero replicates.

The target is the independent product of uniform positional permutation laws. A closure-safe callback invokes the verified shuffle, then verified finite repetition supplies independence. Generic framed callers and zero-replicate/infinite-credit tests pass without any distinctness assumption.

## Batch006

Five samplers accepted with immutable Batch006 callers and receipt. Independent
sequential builds, source review, framed arbitrary ENNReal credits, boundary and
infinite-credit examples, and standard-axiom checks pass without warnings.

StoppedExtrema defines minima/maxima through independent observation vectors,
then a positive-count mixture. The count support is a supplied almost-sure fact;
there is no uniform count bound or finite moment assumption. Generic Gibbs
specifications explicitly cover countable state spaces with supplied conditional
kernel contracts; they do not claim unverified continuous-state callbacks.

### `Occil.General.stoppedMinimum`

Accepted `SampLib.StoppedMinimum.stoppedMinimum_distSpec`, SHA-256
`d5f0aa4a5705791bd6fd0554805175a678c8089ce901b1cece72460c6c4874ea`.

Domain: Every normalized integer observation callback and independent almost-surely positive natural count callback; no count bound or moment assumption.

The law mixes the minima of independent finite observation vectors over the supplied count distribution. Its expectation conditions on count and the initial observation, with a separate product-Fubini update identity. Program logic calls the supported positive counter, first observation and a direct finite min fold. Arbitrary resources/credits, count1, deterministic repeated extrema and infinity pass.

### `Occil.General.stoppedMaximum`

Accepted `SampLib.StoppedMaximum.stoppedMaximum_distSpec`, SHA-256
`07c2d640a020966e62d1c500df0203b1ec8ceab60183ed355b17319c7e2dac61`.

Domain: Every normalized integer observation callback and independent almost-surely positive natural count callback; no count bound or moment assumption.

The independent-vector maximum and positive-count mixture give the exact normalized target. The symbolic proof mirrors the two deterministic comparison branches and a finite decreasing count. Both extrema share mathematical iid-fold laws but retain their actual distinct program comparisons. Framing, count1, deterministic repeated observations and arbitrary infinite credits pass.

### `Occil.General.markovTrajectory`

Accepted `SampLib.MarkovTrajectory.markovTrajectory_distSpec`, SHA-256
`c6cf78318eb965b24bee06db9de9525bc574a29c9b85c00140190625242f34c3`.

Domain: Every square positive-total-row nonnegative integer matrix, valid initial state and natural step count; zero steps also support arbitrary matrix/initial values without a uniform-integer primitive.

The target is the canonical successive-state Markov path, excluding its initial state. Conditioning on the first transition yields the expectation identity. Program logic samples one supported transition then recurses under a list constructor through the checked context rule. An alternating matrix yields exactly [1,0,1] from initial0 after3steps; generic framed/zero/infinity callers and standard axioms pass.

### `Occil.General.gibbsSweep`

Accepted `SampLib.GibbsSweep.gibbsSweep_distSpec`, SHA-256
`40bde9224d47fc40567ae2cf8d741184fb2249fa68d222b61887d83ce607feb3`.

Domain: Every natural sweep dimension, countable measurably encoded state space and normalized supplied coordinate kernels; callback contracts are required only for indices below dimension.

The target is ordered composition of the supplied conditional kernels. Product conditioning gives the continuation, and generic invariance follows when each coordinate preserves a common target. The program simply calls coordinates in increasing order, passing the updated state. Independent noncommuting affine updates verify order/current-state use; dimension0 permits arbitrary callback and initial values without randomness. Framed credits and infinity pass.

### `Occil.General.randomScanGibbs`

Accepted `SampLib.RandomScanGibbs.randomScanGibbs_distSpec`, SHA-256
`5d86ec27826d03cea4b152e40b9b5b56013bcb2c47273b55d2ccdbef382a4c17`.

Domain: Positive coordinate count, countable measurable encoded states, supplied normalized coordinate callbacks and all natural update counts; a separate zero-update theorem accepts arbitrary callback/initial values without uniform randomness.

The target iterates the uniform mixture of coordinate kernels. Its expectation conditions first on the selected coordinate, then its updated state; target invariance follows from common coordinate invariance. Straight-line CTE performs uniform choice, callback and recursion. Single-coordinate repeated updates, identity-kernel stationarity, zero-update resources, arbitrary credits and infinity pass.

## Batch007

Two samplers accepted, with immutable Batch007 caller and receipt. Independent
builds, mathematical and program source review, caller-resource framing, exact
finite probabilities, boundary/infinite-credit and standard-axiom checks pass
without warnings.

RandomGraph uses an independent Boolean product and a canonical upper-triangle
edge list. Reservoir uses an independent closed ordered-slot mass law, rather
than assuming the returned slots have a uniformly random order. Its substantive
incoming-mass proof establishes the transition identity, normalization and exact
finite-scan law. The public output is a pure list; the allocated mutable array
remains internal and its ownership is retained through initialization, every
replacement and reading. Total decoding outside the bounded supported slot law
has zero probability. These mathematical supporting modules add no sampler count.

### `Occil.randomGraph`

Accepted `SampLib.RandomGraph.randomGraph_distSpec`, SHA-256
`11292da042163e305e7dc3674921f178a6659e475a88313fe8883053674912a5`.

Domain: Every natural vertex count and Bernoulli callback bias p∈[0,1], including empty/singleton graphs and both deterministic bias endpoints; no random primitive assumption beyond the supplied callback contract.

The canonical upper triangle is identified by membership, no duplicates and strict lexicographic order. A separate independent Bernoulli-vector product is pushed through edge retention. Fubini gives the one-indicator continuation identity; the actual nested row/column program uses it through composable loop specs. Independent n0/n1, p0/p1 with infinite off-support credits, triangle event1/8, generic framing and standard axioms pass.

### `Occil.reservoir`

Accepted `SampLib.Reservoir.reservoir_distSpec`, SHA-256
`77cac185eaa5cc46d11b5fb0fb261d80fc98388dd7684d0c984628e307814643`.

Domain: Every finite list with arbitrary encoder and natural capacity0≤k≤length, including duplicate values, zero capacity, empty input and full capacity.

The target is an independent closed joint law for ordered original-position slots: every surviving initial item stays in its original slot, and an admissible tuple with m later items has mass1/(choose(n,k)·m!). The mathematical incoming-mass argument separates the initial predecessor from available later predecessors, then proves exact normalization and the finite-scan bridge without converting continuation credits to real. Symbolic execution fills the private array, applies uniform replacement tickets, preserves complete ownership, and returns a pure read list. Independent masses1/20 versus1/10, invalid swapped initial/duplicate slot masses0, empty/full capacity, duplicate-value decoder, arbitrary framing and infinity pass.

## Batch008

Five samplers accepted, with immutable Batch008 callers and receipt. Independent
sequential builds, mathematical/program source review, caller framing, exact
boundary probabilities, arbitrary infinite credits and standard-axiom checks
pass without warnings.

DistributionMapSupported transports output encodings on a measurable almost-sure
support, with deliberate encoder disagreement on a null output and an arbitrary
caller resource. BooleanEvent identifies an event observation with its full
Bernoulli law. IntegerThreshold counts accepted integer ranks exactly; interval
support is transported under signed translation. FiniteCDF independently
identifies the quantile law by its CDF, while Bracket isolates all bisection
arithmetic. Column-length support and finite repetition justify safe transpose
lookups. Closedness/value witnesses only normalize syntax and use existing
checked rules. All are supporting modules, adding no sampler count.

### `Occil.General.permutationTest`

Accepted `SampLib.PermutationTest.permutationTest_distSpec`, SHA-256
`0aff291aaf7730f2e2e4c905c6af9c79ffe8fe1125b139951ea04cf5ceb25f21`.

Domain: Every finite observation list, arbitrary valid deterministic integer statistic and natural replicate count, including empty input, duplicates and zero trials.

The bias is the exact uniform positional-permutation probability that the null statistic is at least the observed one, including ties. Independent trials give the Binomial law; the encoder returns(count+1,replicates+1). The sole expectation argument transports the Boolean event and uses the shifted Binomial recurrence. Straight symbolic execution calls shuffle and the pure statistic. Framed arbitrary credits, constant-statistic tie bias1, zero trials, exact(1,1) encoding and infinity pass.

### `Occil.General.groupedPermutation`

Accepted `SampLib.GroupedPermutation.groupedPermutation_distSpec`, SHA-256
`6cc32439970ff242db046d927c763a63a575796294ecd6fb130982550d15364c`.

Domain: Arbitrary observation types/encoders and nonnegative group sizes summing to the observation count; zero sizes, empty observations and duplicate values are included.

The target is the uniform position-permutation law pushed through consecutive grouping. The mathematical expectation is change of variables. Program logic validates total size, samples one shuffle, then executes deterministic exact splits. Explicit top measurable output space permits arbitrary observation types. Empty input produces the requested empty groups; mixed zero sizes and duplicate values, framing and infinite credits pass.

### `Occil.General.pdfRejection`

Accepted `SampLib.PdfRejection.pdfRejection_distSpec`, SHA-256
`1c6f54b2a5b19d630dbe51bc304d938e9ddf3426be7ca786bf1df99a0263bff1`.

Domain: Every signed nonempty half-open integer proposal interval, positive integer envelope, natural height bounded on that interval, and positive total acceptance mass. The pure density callback is specified only on proposal points.

The normalized target weights the uniform grid proposal by height/envelope. The shared AcceptedProposal conservation lemma and bounded amplification factor1+acceptanceMass establish rejection termination, including certain acceptance. IntegerThreshold verifies the actual strict integer comparison. Independent signed two-point tests show a zero-height atom with arbitrary, potentially infinite credit contributes zero and the accepted law returns the other point; certain acceptance mass1, threshold endpoints, framing and infinity pass.

### `Occil.General.latinHypercube`

Accepted `SampLib.LatinHypercube.latinHypercube_distSpec`, SHA-256
`001e20c468e643193ccfa67ca2b88bf9f287942822ac0ced86b436da8fc4e6d7`.

Domain: Every integer grid with1≤count≤scale and every positive dimension.

The canonical law independently samples shuffled rounded-stratum columns and transposes them into count point rows. Almost-sure column lengths justify every lookup; the transpose is a deterministic pushforward. The CTE proof composes finite repetition, support and pure row construction. Closed value witnesses perform only known binder normalization. Independent transpose ordering, singleton-grid two-dimensional point, generic framing and infinite credits pass. No false whole-grid uniform-marginal claim is made.

### `Occil.General.inverseCDF`

Accepted `SampLib.InverseCDF.inverseCDF_distSpec`, SHA-256
`9107835711d0cd008ce22beb05f24cdf68cb4e18d9977ce46557c27f4a2365b1`.

Domain: Positive integer CDF denominator, signed nonempty closed integer grid, nondecreasing CDF in[0,scale] with cdf(upper)=scale; singleton grids, plateaus and nonzero lower atoms are included. Oracle contracts are required only on the grid.

The independent first-reaching-rank quantile is proved to have exactly the supplied CDF, including its lower-endpoint atom. Bisection preserves a bracket around this fixed quantile and strictly reduces its integer width. The program proof executes the uniformly selected rank followed by deterministic well-founded search. Independent lower-atom/plateau CDF1/4, singleton scale1 law, framing and infinity tests pass.

## Batch009

Three samplers accepted with immutable callers and receipt. Independent sequential
builds, source review, full-credit framed clients and axiom audits pass without
warnings. All inspected axioms are propext, Classical.choice and Quot.sound.

The owned distribution template preserves an arbitrary private resource and
threads it linearly through actual independent repetition. A concrete heap-load
sampler repeatedly reads an owned cell and restores that ownership, including
zero repetitions and infinite credits, while preserving an unrelated caller
resource. The vector-store adapter derives from the existing array ownership
rule. AliasMass independently regroups incoming alias edges and identifies the
normalized categorical law from exact integer mass conservation. A concrete
two-column table has weights1:3; its category-zero expectation is1/4 and infinite
credit at an absent output costs zero. AliasTable verifies actual voseDraw and
restores both arrays, including its identity-alias shortcut. These are supporting
modules, not additional samplers; constructor correctness remains a separate
obligation.

### `Occil.derangement`

Accepted `SampLib.Derangement.derangement_distSpec`, SHA-256
`6be6a343ce2eceae56770d8b2ddfdbdb5cfc7a8e027a776e5389cf0047bff0be`.

Domain: Every natural size other than one, including zero.

The independent target is the uniform law on all fixed-point-free position permutations, with exact acceptance !n/n! and atom mass1/!n. Actual integer range, uniform shuffle, fixed-point checker and generic rejection compose directly. The acceptance theorem and syntax transports are prepared before resource introduction. Independent tests include empty size, size two, an accepted size-four double transposition with mass1/9, infinite credit and arbitrary caller framing. The double transposition distinguishes all derangements from just full cycles.

### `Occil.General.metropolisHastings`

Accepted `SampLib.MetropolisHastings.metropolisHastings_distSpec`, SHA-256
`a8cccf0cd6f0217f88aca489c24ef5cd1321155205870f25a4205ccad777cb09`.

Domain: Finite normalized rational proposal rows with positive denominators, natural target weights and a positive-weight initial state; arbitrary natural steps. An unrestricted zero-step theorem permits arbitrary callback and initial values without random primitives.

The normalized target kernel uses the exact capped opposing-flow ratio. Detailed balance and invariant target follow from the min-flux identity; finite-step law from a fixed start is stated separately. The common CTE executes pure target/proposal callbacks, supported proposal, capped rational acceptance and the recursive branch. Independent zero-forward-probability and zero-target examples remain at the positive state for every step; infinite credit at the impossible state contributes zero. Rational cap endpoints, invariance, unrestricted zero steps and arbitrary resource framing pass.

### `Occil.General.metropolis`

Accepted `SampLib.SymmetricMetropolis.metropolis_distSpec`, SHA-256
`76a8446a9f84be25d3dc1516ce3c0fd54abe86c7e98462b80b5c5884a15af6eb`.

Domain: Countable encoded states, normalized proposal kernels, natural target weights and positive-weight initial state, all natural steps; proposal symmetry is needed only for target invariance. Unrestricted zero steps require no callback contract or random primitive.

The source constant q=1 is correctly treated as a ratio surrogate, independently of the actual proposal kernel. The shared transition core proves the exact finite-step law for any proposal; a separate symmetry hypothesis proves detailed balance and target invariance. Pure mathematical expectation preservation precedes obvious callback/acceptance/recursion steps. Independent zero-target deterministic-flip example, arbitrary infinite credits, capped acceptance, unrestricted zero and framed clients pass.

## Batch010

Three general integer-grid samplers accepted with immutable callers and receipt.
Independent sequential target builds, full mathematical/program source review,
quantitative boundary clients, arbitrary infinite credits, caller framing and
standard-three-axiom audits pass warning-free. The laws describe the actual
discrete grid implemented by these programs.

The new linear-bin support proves positive accepted mass even when the left
endpoint is zero, and bounded amplification handles certain acceptance too.
Gauss summation identifies the half-open grid mass independently of runtime
preprocessing. Positive-weight support discards only null categorical outputs;
zero-density bins remain valid inputs. These modules are supporting mathematics
and logic, adding no sampler count.

### `Occil.General.discreteCDF`

Accepted `SampLib.DiscreteCDF.discreteCDF_distSpec`, SHA-256
`b1c8a458be2afe4d796e6790970bca315a3ae4dba85938b2693660ec7082a4df`.

Domain: Every nonnegative nondecreasing finite cumulative table with positive final mass, including leading zeros, plateaus, singleton tables and a nonzero lower atom.

The target is the independently characterized finite quantile law: its CDF equals the supplied cumulative mass divided by the final mass. Deterministic table search preserves a fixed quantile bracket and decreases width; the outer proof draws a uniform rank. Independent table[0,0,4,4] tests show exact zero cumulative mass through position1 and full mass at position2. Generic arbitrary-credit caller framing and standard-axiom checks pass.

### `Occil.General.piecewiseConstant`

Accepted `SampLib.PiecewiseConstant.piecewiseConstant_distSpec`, SHA-256
`886bcb24450ee388b76dafc6627663bbff180c4b13bf28871a931c45773f97f4`.

Domain: Every strict signed integer partition with matching nonnegative natural bin heights and positive total grid mass; zero-height bins are included.

Exact bin masses are width times density height, followed by uniform position within the selected bin. The mathematical expectation reuses the independently verified histogram mixture after the coefficient identity. Deterministic area preprocessing and syntax preparations precede clear categorical selection and interval sampling. An independent unequal-width grid[-1,0,2] with heights[2,1] has atoms1/2 at−1 and1/4 at1; the full arbitrary-credit expectation is checked, as are framing and infinity.

### `Occil.General.piecewiseLinear`

Accepted `SampLib.PiecewiseLinear.piecewiseLinear_distSpec`, SHA-256
`77329e3878396e8ca101a6c2757a9cccd98e74db08d2ce106f08d9618ded5b90`.

Domain: Every strict signed integer vertex grid with nonnegative natural heights and positive total half-open interpolated grid mass, including zero vertices and zero-profile bins.

Gauss summation independently proves the source bin profile is twice its actual half-open interpolated density mass. Positive bins admit bounded integer-threshold rejection; almost-sure positive categorical support excludes empty profiles without narrowing the input domain. The CTE composes deterministic profile preprocessing, bin selection and the verified bin retry, with pure transports prepared before execution. Independent rising profile heights[0,3,6] has exact profile6 and zero credit contribution at its zero-height point even for infinity; generic framing and normalized infinite credits pass.

## Batch011

Three samplers accepted with immutable callers and receipt: generic CFTP, its
concrete matrix wrapper (derived), and finite-grid slice sampling. Independent
sequential target builds, mathematical/program source review, actual two-step
coalescent clients, sparse slice probabilities, arbitrary credits and resources,
and standard-three-axiom audits pass warning-free. SliceStep remains fully
reviewed support; no transition/iteration double counting occurs.

Weighted amplification is derived from existing error-credit induction using a
state potential uniformly at least one. Typed RandomMap transports its encoding
only on its proved almost-sure support. Uniform finite-grid proposals reuse the
verified signed interval sampler. The CFTP potential is explicitly measured in
remaining extension rounds; it is not a claimed bound on callbacks or primitive
execution costs. Selective MeasureTheory type openings keep convolution notation
from conflicting with Iris separation.

### `Occil.General.couplingFromPast`

Accepted `SampLib.CouplingFromPast.couplingFromPast_distSpec`, SHA-256
`eec44bd582231647a80c26d6906c39d32da7cec43f7d8a623728d9f9781607a0`.

Domain: Every normalized iid map law on a nonempty finite state space, a stationary probability law, and positive probability of coalescence in some finite iid word. No single-map or strictly-positive-matrix hypothesis is imposed.

Chronological histories preserve stationary continuation credit when older iid maps are prepended. Coalescence identifies this credit with the common image. A bounded remaining-round potential funds an amplified extension only while histories remain noncoalescent; it makes no primitive-runtime expectation claim. The CTE visibly checks all images, samples and appends older maps, and doubles the horizon. The block hypothesis is proved equivalent to the finite-word positivity condition. An actual deterministic callback climb=[1,2,2] coalesces first after two maps, targets Dirac2 and preserves arbitrary caller resources, including infinite credit off its target support.

### `Occil.General.perfectFiniteChain`

Accepted `SampLib.PerfectFiniteChain.perfectFiniteChain_distSpec`, SHA-256
`f13495eb91efbd736c430ffb75b765ef9fab0769b6aaad43df0dd349031eb0ac`.

Domain: Every nonempty square matrix of natural transition weights with positive row totals, stationary probability law, and positive coalescence probability for a finite word of its actual independently sampled shared-map law; zero matrix entries are allowed.

This derived implementation calls the verified concrete random-map sampler and generic CFTP. Almost-sure valid integer destination lists transport to finite-function encodings; coordinate marginals identify the matrix kernel. Independent sparse deterministic three-row initialization gives the actual two-step-coalescing map[1,2,2], stationary Dirac2 and a framed public wrapper client. Generic arbitrary-credit matrix framing and standard-axiom checks pass.

### `Occil.General.sliceSampler`

Accepted `SampLib.SliceSampler.sliceSampler_distSpec`, SHA-256
`6cd79f2b06ba93bedb3e45400e7f2b7f81008895d0a42db13be0e7e646bd8b59`.

Domain: Every positive-width signed integer proposal grid with natural density weights, positive grid starting state and natural transition count. Additional public specs cover arbitrary outside-grid starting values with positive cap bounded by a grid anchor, and unrestricted zero steps with arbitrary values and no random-primitive assumption.

The canonical kernel uniformly samples an integer height, then a uniform point in its nonempty slice. Symmetric shared-height reciprocal-cardinality flux proves detailed balance and target invariance. The explicit grid-anchor equivalence preserves the full valid outside-grid cap domain. Source logic composes verified height sampling, rejection and supported finite iteration. Independent sparse weights[0,1,2] give mass1/4 to state1 at cap2; infinite credit at state0 contributes zero, and every finite iterate preserves the normalized target. Framed outside-start and unrestricted-zero clients pass. SliceStep is fully checked support only, not a second counted technique.

## Batch012

Four samplers accepted with immutable callers and receipt, one derived.
Independent sequential builds, complete new mathematical/program source review,
quantitative clients, arbitrary credits and caller resources, and standard-three-
axiom audits pass warning-free. Canonical Wallenius word/count mathematics and
NatCounters are reused from the discrete reviewer's immutable Batch011 receipt;
the new actual multicolor consumers, urn validator and weight construction were
independently reviewed here.

Vose's finalized workspace entries are logically full only in the residual
invariant; the proof does not invent heap writes absent from the program. Exact
threshold-plus-incoming-alias conservation identifies categorical masses. The
constructor returns ownership, the actual draw preserves it, and owned iteration
yields the pure iid output list. All construction and draw operations remain
support for the single public Vose sampler.

### `Occil.Weighted.uniformBinaryFloat`

Accepted `SampLib.UniformBinaryFloat.uniformBinaryFloat_distSpec`, SHA-256
`3c0aedda462e07b3cade01880c97642507a658e2b61f020ad1642455129c3696`.

Domain: Every natural mantissa precision and leading-zero cap, including zero precision and zero cap.

The canonical law decodes an independent capped fair-geometric leading-zero count and uniform integer mantissa. Reaching the cap returns(0,0); otherwise the exact integer significand/exponent pair is returned. One Fubini/capped-geometric split funds a finite symbolic-execution induction. Independent precision-zero/cap-two exact pair mass1/4, cap-zero Dirac law, arbitrary infinite credits and caller framing pass. No IEEE or continuous-uniform identification is claimed.

### `Occil.DiscreteExtra.walleniusMultivariate`

Accepted `SampLib.WalleniusMultivariate.walleniusMultivariate_distSpec`, SHA-256
`4dbde6c433c43d1346c72d969173574f84cc811ccf57fcf914bdc773778d765c`.

Domain: Natural population counts and request at most their sum, matching positive integer odds, including empty urn with zero request and zero-population classes.

The target is the canonical successive weighted color-word likelihood pushed to ordered color counts. This shared mathematics was independently accepted in ExpansionDiscreteBatch011. The accumulator expectation and first-color preservation isolate the argument; source logic validates, initializes zero counts, selects a supported positive population color, updates two counters and recurses. Independent three-color sparse urn tests distinguish weighted ordered word masses1/4 and3/4 and verify their count encoding; concrete full-request and empty-zero source clients, framing and infinite credits pass.

### `Occil.DiscreteExtra.multivariateHypergeometric`

Accepted `SampLib.MultivariateHypergeometric.multivariateHypergeometric_distSpec`, SHA-256
`0ad699aff59a92c31183940c5bec70f73177b818b5da4990b64acd6b502b8176`.

Domain: Every natural finite multicolor population and natural request at most its sum, including empty input, zero-population colors and zero draws.

This derived implementation constructs unit odds and applies the verified multicolor Wallenius sampler. The shared equal-odds product theorem identifies the ordinary successive without-replacement urn probabilities. An independent sparse three-color ordered word has probability1/2 under unit odds, distinct from its weighted counterpart. Generic framed clients and full-credit normalization checks pass.

### `Occil.WeightedVariants.voseSamples`

Accepted `SampLib.VoseSamples.voseSamples_distSpec`, SHA-256
`d2c59e6f15a65728c719d8dfd9303edaf7acaf99846f9e2c113bd7c74c016670`.

Domain: Every finite list of nonnegative natural weights with positive total and every natural sample count, including zero counts and zero-weight categories.

Actual preprocessing allocates and fills workspace, threshold and alias arrays, then balances small/large columns under per-category residual mass conservation. Strict worklist decrease proves termination; equal total capacity forces final exact categorical mass. The constructor returns genuine owned table arrays. Actual voseDraw preserves those resources, and the owned repetition template gives independent categorical draws before a deterministic list pushforward. Independent initialized sparse-weight two-draw source clients, exact iid list probability1/4, zero-weight infinite-credit exclusion, zero count and arbitrary-resource framing pass. Constructors and draw helpers add no headline count.

## Batch013: countable Metropolis correction and owned Fenwick inversion

Two existing sampler evidence rows are replaced by stronger NEW countable public
theorems; one owned Fenwick sampler is added. No historical Batch009 artifact or
frozen proof is changed. My earlier Batch009 Metropolis scope wording overstated
the finite wrappers, and the core classification overlooked the actual thin
MH specialization. This correction records the source-based derived label and
newly proved countable interfaces, rather than merely narrowing the scope claim.
The two Metropolis techniques retain their existing counts.

The owned Fenwick specification is explicitly marked owned in both receipt and
candidate row. Initialization, signed updates, total-zero reachability and full
resource-preserving repeated draws are checked against actual source operations.
No fresh-location pure law or added runtime wrapper is claimed.

The deterministic PiBounds gateway is supporting evidence only: exact unreduced
integer triples for reciprocal-arctangent partial sums and their cross-multiplied
Machin combination, with weak-language framed callers and both parity cases.
Its analytic interpretation and counted pi samplers remain the factories group's
separate responsibility. Raw interface sources are frozen and pinned.

Independent sequential builds, source review, arbitrary-credit/resource callers,
exact boundary laws and standard-three-axiom audits pass warning-free.

### `Occil.General.metropolisHastings`

Accepted `SampLib.CountableMetropolisHastings.metropolisHastings_distSpec`, SHA-256
`4e53af8d7f867c61364a0b0d4c03aed17ddb5a2f62bcd4107602e999a45041c7`.

Domain: Every countable encoded state space, normalized proposal measures whose singleton probabilities are represented by natural numerators and positive natural denominators, natural target weights and a positive-weight initial state, all natural transition counts. Unrestricted zero transitions require no callback contracts or random primitive.

The new public API links each supplied normalized proposal measure to its exact rational singleton probabilities. Countability gives almost-sure positive forward numerator; the already verified general ratio kernel proves the actual source finite-step law. No finite-state class remains. Independent actual Nat callbacks use the deterministic forward proposal x↦x+1 and its truthful rational probabilities; the missing reverse edge makes Hastings reject every proposal, giving Dirac(initial) for every step. Generic full-credit framing and unrestricted-zero clients pass.

### `Occil.General.metropolis`

Accepted `SampLib.CountableMetropolis.metropolis_distSpec`, SHA-256
`710ca1317bbd3617847846e130f307f0b5fe5c3a0e07f58db8b7cf01d028fc14`.

Domain: Every countable encoded state space, arbitrary normalized proposal measures, natural target weights and a positive-weight initial state, all natural transition counts. Symmetry is not required for the execution law; a stationary probability-target interpretation additionally needs symmetry and normalizability. Unrestricted zero transitions require no callback contracts or random primitive.

The actual source is a direct Metropolis–Hastings specialization supplying the constant ratio callback(1,1), so the technique is derived under the thin-wrapper policy. The new public theorem removes the old finite-state wrapper restriction while preserving all frozen proofs. Independent actual Nat callbacks with forward proposal x↦x+1 and constant target weight return exactly initial+steps; the contrast with truthful Hastings rejection tests the ratio-surrogate distinction. Generic countable framed clients, arbitrary infinite credits and unrestricted zero pass.

### `Occil.WeightedVariants.fenwickDraw`

Accepted `SampLib.FenwickDraw.fenwickDraw_ownedDistSpec`, SHA-256
`53a2b46d0d4862d87b0f5a789e24089f54eaad30f4344acc0bba23501f8ba75c`.

Domain: Every finite natural weight vector of positive total and every caller-owned exact Fenwick representation, including zero weights and non-power-of-two lengths. Supporting constructor accepts every positive-total natural list; supporting setter accepts every valid position and natural replacement, including a zero-total result. Bare ownership permits total zero, while drawing requires positive total.

The target is the canonical categorical law of the current weight vector. Genuine one-based dyadic interval sums and a fixed independently defined inverse-CDF interval characterize binary lifting. A uniform rank then determines exactly its categorical category, preserving the full owned total reference, values and n+1 tree cells. Constructor and signed replacement proofs establish and maintain this representation. Independent actual sparse length-five initialize→draw with arbitrary external resource, draw→read unchanged total reference, owned iid repetition, and initialize[7]→set0 prove meaningful inhabited ownership. A complete sparse search path exercises out-of-range skip, comparison, exact-boundary and zero-cell advances. Signed decreases, impossible-output infinite credits and standard axioms pass. No heap-free sampler wrapper is invented.

## Batch014: Walker sampling and derived-wrapper metadata corrections

Walker alias sampling is accepted with immutable callers and receipt. Independent
sequential target builds, full mathematical/program source review, exact ordered
iid probability1/4, impossible-output infinite credits, zero repetitions, caller
framing and standard-three-axiom audits pass warning-free.

Accepted `SampLib.AliasSamples.aliasSamples_distSpec`, SHA-256
`a56a0fb056272598612fb0576f434680c85b76ef44727620e517e072b93700b5`.

Domain: Every finite list of nonnegative natural weights with positive total and every natural sample count, including zero repetitions and zero-weight categories.

The independent target is the categorical iid position-vector law. Private-array
initialization, read-only small/large searches and strict-donor transfers maintain
per-category deficit conservation. Total remaining work forces exact terminal
category masses, while pending-column cardinality strictly decreases. The actual
two-uniform draw restores both table arrays; owned repetition gives independent
outputs. Sparse interior-zero input[1,0,1], actual source initialization and
sampling, exact ordered two-draw probability1/4, zero count, and infinite credit
on impossible[1,1] pass.

The main CTE proof uses two named beta steps and one proved pure source-opening
transport, followed by ordinary execution. A subtype witness caches the normalized
expression with a kernel-checked equality to the original opened source. It adds
no duplicate source quotation, new semantic rule or custom metaprogram. BetaStep
is a direct specialization of the existing checked pure-step-context rule;
an arbitrary-context/body/value/resource continuation caller works under weak
WP assumptions, including values with named free variables.

Five existing rows are reclassified as derived under the substantive-construction
policy. Their proofs, laws, domains, source hashes and historical receipts are
unchanged; fresh framed boundary callers and axioms are included here. Public
sampler-name counts do not increase from these corrections. PositiveComposition
remains core for its full cut/composition bijection, and LatinHypercube1D remains
core for combining independent stratification and shuffling.

- `Occil.General.bootstrap`: The actual term computes the original sample size and independently repeats the already counted sampleWithReplacement sampler. Previous immutable receipt: `agent-docs/reviews/ExpansionStructuredBatch003.json`.
- `Occil.General.permutationSamples`: The actual term independently repeats the already counted shuffle sampler. Previous immutable receipt: `agent-docs/reviews/ExpansionStructuredBatch005.json`.
- `Occil.General.latinHypercube`: The actual multidimensional term independently repeats the already counted one-dimensional Latin-hypercube law and transposes the resulting columns. Previous immutable receipt: `agent-docs/reviews/ExpansionStructuredBatch008.json`.
- `Occil.General.groupedPermutation`: The actual term samples the already counted shuffle and deterministically partitions its output into the prescribed groups. Previous immutable receipt: `agent-docs/reviews/ExpansionStructuredBatch008.json`.
- `Occil.weakComposition`: The actual term samples positiveComposition(n,total+n) and subtracts one from each coordinate, a trivial bijective shift of the existing construction. Previous immutable receipt: `agent-docs/reviews/ExpansionStructuredBatch004.json`.
