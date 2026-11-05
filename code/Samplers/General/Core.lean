import Samplers.Combinatorial
import Samplers.Continuous.Rejection
import Samplers.Lazy

/-!
General sampling constructions from `randomfunc.html` and `randmisc.html`.

Collections use the project's `inl(unit)` / `inr((head,tail))` list encoding.
Numerical callbacks operate on an integer grid: an integer x represents x/scale.
Grid algorithms specify their discretization explicitly; Markov-chain steps are
finite-time transitions, not a claim of an exact stationary draw.
-/
namespace Occil.General
open ProbLang
variable {rT : Type _}

/-! ## Small collection operations -/

@[pl_fold] def append : Exp rT := pl%
  rec join xs ys := case! xs
    | inl(u) => ys
    | inr(p) => inr((fst(p), join (snd(p)) ys))

@[pl_fold] def map : Exp rT := pl%
  rec apply f xs := case! xs
    | inl(u) => inl(#())
    | inr(p) => inr((f (fst(p)), apply f (snd(p))))

@[pl_fold] def tail : Exp rT := pl%
  fun xs, case! xs | inl(u) => fail | inr(p) => snd(p)

@[pl_fold] def fold : Exp rT := pl%
  rec apply combine initial xs := case! xs
    | inl(u) => initial
    | inr(p) => apply combine (combine initial (fst(p))) (snd(p))

/-- Uniform character/item sequences; output is a list, not a host string. -/
@[pl_fold] def randomString : Exp rT := pl%
  fun alphabet size, &Occil.sampleWithReplacement alphabet size

/-- Uniform integral timestamp in an inclusive application-specified epoch range. -/
@[pl_fold] def randomDateTime : Exp rT := pl%
  fun earliest latest, &Occil.rndIntRange earliest latest

/-! ## Inverse transform and density sampling -/

/-- A deterministic quantile callback evaluated at a uniform probability grid.
`quantile scale p` receives p in 1..scale-1; scale must exceed one. -/
@[pl_fold] def inverseQuantile : Exp rT := pl%
  fun scale quantile u,
    if scale <= #1 then fail else
      quantile scale (#1 + &Occil.uniformInt (scale - #1))

/-- Select the first cumulative integer weight strictly exceeding a draw.
Cumulative weights must be nondecreasing, nonnegative and end at a positive total. -/
@[pl_fold] def discreteCDF : Exp rT := pl%
  fun cumulative u,
    let n := &Occil.length cumulative;
    if n <= #0 then fail else
      let total := &Occil.getAt cumulative (n - #1);
      let value := &Occil.uniformInt total;
      let search := (rec find lo hi :=
        if lo = hi then lo else
          let mid := (lo + hi) / #2;
          if value < &Occil.getAt cumulative mid then find lo mid
          else find (mid + #1) hi);
      search #0 (n - #1)

/-- Integer-grid quantile inversion by bisection. The monotone callback
`cdf x` returns cumulative mass in 0..scale and `cdf upper = scale`.
The output is the smallest grid point whose CDF reaches a rank in 1..scale. -/
@[pl_fold] def inverseCDF : Exp rT := pl%
  fun scale cdf lower upper u,
    if (scale <= #0) || (upper < lower) then fail else
      let rank := #1 + &Occil.uniformInt scale;
      let search := (rec bisect lo hi :=
        if lo = hi then lo else
          let mid := lo + (hi - lo) / #2;
          if rank <= cdf mid then bisect lo mid else bisect (mid + #1) hi);
      search lower upper

/-- Uniform-proposal PDF rejection on [lower,upper). `density x` is an integer
height between zero and envelope. This exactly samples the resulting grid PMF;
it approximates a continuous density when the supplied grid is a discretization. -/
@[pl_fold] def pdfRejection : Exp rT := pl%
  fun density lower upper envelope u,
    if (upper <= lower) || (envelope <= #0) then fail else
      let draw := (rec retry u :=
        let x := &Occil.rndIntExcRange lower upper;
        let height := density x;
        if (height < #0) || (envelope < height) then fail else
        if &Occil.uniformInt envelope < height then x else retry #());
      draw #()

/-- Rejection in any bounded shape. Proposal values may be structured vectors;
`member` must be a deterministic Boolean predicate with positive acceptance mass. -/
@[pl_fold] def shapeRejection : Exp rT := pl%
  fun proposal member u, &Occil.rejection proposal member #()

/-- Constant-density bins. `points` has one more entry than `heights`;
points strictly increase and heights are nonnegative. Returns an integer-grid x. -/
@[pl_fold] def piecewiseConstant : Exp rT := pl%
  fun points heights u,
    if &Occil.length points = &Occil.length heights + #1 then
      let weights := (rec areas xs hs := case! hs
        | inl(v) => inl(#())
        | inr(hp) =>
          let left := &Occil.getAt xs #0;
          let right := &Occil.getAt xs #1;
          let h := fst(hp);
          if (right <= left) || (h < #0) then fail else
            inr(((right - left) * h, areas (&tail xs) (snd(hp)))));
      let bin := &Occil.weightedChoice (weights points heights);
      let lower := &Occil.getAt points bin;
      let upper := &Occil.getAt points (bin + #1);
      &Occil.rndIntExcRange lower upper
    else fail

/-- Piecewise-linear density on an integer grid. `vertices` contains (x,height)
pairs in increasing x order. Each bin includes its left endpoint and excludes its
right endpoint. The bin weights use the exact sum of its interpolated grid heights,
not continuous trapezoid areas; this avoids a variable-bin-width normalization bias. -/
@[pl_fold] def piecewiseLinear : Exp rT := pl%
  fun vertices u,
    let weights := (rec areas xs := case! xs
      | inl(v) => fail
      | inr(p) => case! snd(p)
        | inl(v) => inl(#())
        | inr(q) =>
          let a := fst(p);
          let b := fst(q);
          let width := fst(b) - fst(a);
          let ha := snd(a);
          let hb := snd(b);
          if (width <= #0) || (ha < #0) || (hb < #0) then fail else
            inr(((width + #1) * ha + (width - #1) * hb, areas (snd(p)))));
    let bin := &Occil.weightedChoice (weights vertices);
    let a := &Occil.getAt vertices bin;
    let b := &Occil.getAt vertices (bin + #1);
    let left := fst(a);
    let width := fst(b) - left;
    let ha := snd(a);
    let hb := snd(b);
    let envelope := (if ha < hb then hb else ha);
    let draw := (rec retry u :=
      let offset := &Occil.uniformInt width;
      let height := ha * (width - offset) + hb * offset;
      if &Occil.uniformInt (width * envelope) < height then left + offset
      else retry #());
    draw #()

/-! ## Sampling with progressively refined information -/

/-- A bounds callback returns numerators `(lower,upper)` at denominator 2^level.
Bounds must enclose a probability p and converge to p. One shared lazy U is compared
against every refinement; fresh U at each level would change the distribution. -/
@[pl_fold] def refinedCoin : Exp rT := pl%
  fun bounds u,
    let bag := &Occil.newUniformBag #();
    let refine := (rec decide level denominator :=
      let interval := bounds level;
      let lo := fst(interval);
      let hi := snd(interval);
      if (lo < #0) || (hi < lo) || (denominator < hi) then fail else
      if &Occil.uniformBagLess bag lo denominator then #true else
      if &Occil.uniformBagLess bag hi denominator then
        decide (level + #1) (denominator * #2)
      else #false);
    refine #1 #2

/-- Compare a shared U with a cumulative-probability oracle.
`bounds index level` gives CDF numerators with denominator 2^level. -/
@[pl_fold] def refinedCDFComparison : Exp rT := pl%
  fun bag bounds index,
    let refine := (rec decide level denominator :=
      let interval := bounds index level;
      let lo := fst(interval);
      let hi := snd(interval);
      if (lo < #0) || (hi < lo) || (denominator < hi) then fail else
      if &Occil.uniformBagLess bag lo denominator then #true else
      if &Occil.uniformBagLess bag hi denominator then
        decide (level + #1) (denominator * #2)
      else #false);
    refine #1 #2

/-- Finite inverse-CDF sampling when only improving probability bounds are known.
The bounds enclose a normalized, monotone CDF and shrink to its values. -/
@[pl_fold] def incompleteInformation : Exp rT := pl%
  fun size bounds u,
    if size <= #0 then fail else
      let bag := &Occil.newUniformBag #();
      let search := (rec bisect lo hi :=
        if lo = hi then lo else
          let mid := (lo + hi) / #2;
          if &refinedCDFComparison bag bounds mid then bisect lo mid
          else bisect (mid + #1) hi);
      search #0 (size - #1)

/-! ## Markov chains and finite-state perfect sampling -/

/-- A transition matrix is a list of nonnegative integer weight rows. Each row has
positive total; sampling normalizes its row independently. -/
@[pl_fold] def markovStep : Exp rT := pl%
  fun matrix state, &Occil.weightedChoice (&Occil.getAt matrix state)

/-- Exactly `steps` transitions from `initial`, not an exact stationary sample. -/
@[pl_fold] def markovChain : Exp rT := pl%
  rec run matrix initial steps :=
    if steps < #0 then fail else if steps = #0 then initial else
      run matrix (&markovStep matrix initial) (steps - #1)

/-- States visited after each transition, excluding the initial state. -/
@[pl_fold] def markovTrajectory : Exp rT := pl%
  rec run matrix initial steps :=
    if steps < #0 then fail else if steps = #0 then inl(#()) else
      let next := &markovStep matrix initial;
      inr((next, run matrix next (steps - #1)))

/-- Draw a random mapping by independently drawing one destination for each row.
The complete mapping is subsequently reused for every possible starting state. -/
@[pl_fold] def randomMap : Exp rT := pl%
  rec draw matrix u := case! matrix
    | inl(v) => inl(#())
    | inr(p) => inr((&Occil.weightedChoice (fst(p)), draw (snd(p)) #()))

/-- Apply a chronological list of already sampled maps to one initial state. -/
@[pl_fold] def applyMaps : Exp rT := pl%
  rec apply maps state := case! maps
    | inl(u) => state
    | inr(p) => apply (snd(p)) (&Occil.getAt (fst(p)) state)

/-- Propp–Wilson doubling CFTP on finite states 0..size-1. `mapSampler unit`
returns a mapping list of length size. Older maps are prepended and all existing
maps are retained on a failed coalescence test. Requires a stationary target and
almost-sure coalescence for this iid random-mapping representation; it may diverge
for periodic/noncoalescing kernels. -/
@[pl_fold] def couplingFromPast : Exp rT := pl%
  fun size mapSampler u,
    if size <= #0 then fail else
      let evolve := (rec run horizon maps :=
        let first := &applyMaps maps #0;
        let coalesces := (rec all state := if size <= state then #true else
          if &applyMaps maps state = first then all (state + #1) else #false);
        if coalesces #1 then first else
          let older := &Occil.repeatSample mapSampler horizon;
          run (horizon * #2) (&append older maps));
      evolve #1 (inr((mapSampler #(), inl(#()))))

/-- Matrix-based CFTP with a concrete shared-random-map construction. -/
@[pl_fold] def perfectFiniteChain : Exp rT := pl%
  fun matrix u,
    &couplingFromPast (&Occil.length matrix) (fun u, &randomMap matrix #()) #()

/-- Exact rational Metropolis–Hastings transitions. `target x` is an unnormalized
nonnegative integer weight; `proposal x` draws a candidate; `q x y` returns its
normalized proposal probability as (numerator,denominator). The initial target
weight and proposal denominators must be positive. -/
@[pl_fold] def metropolisHastings : Exp rT := pl%
  rec run target proposal q initial steps :=
    if steps < #0 then fail else if steps = #0 then initial else
      let candidate := proposal initial;
      let forward := q initial candidate;
      let reverse := q candidate initial;
      let numerator := target candidate * fst(reverse) * snd(forward);
      let denominator := target initial * fst(forward) * snd(reverse);
      if (numerator < #0) || (denominator <= #0) then fail else
        let accepted := (if denominator <= numerator then #true else
          &Occil.rationalCoin numerator denominator);
        let next := (if accepted then candidate else initial);
        run target proposal q next (steps - #1)

/-- Symmetric-proposal Metropolis, so proposal probabilities cancel. -/
@[pl_fold] def metropolis : Exp rT := pl%
  fun target proposal initial steps,
    &metropolisHastings target proposal (fun x y, (#1, #1)) initial steps

/-- One coordinate-update sweep. `conditional index state` samples a new complete
state with just that coordinate changed; its conditional law is a caller contract. -/
@[pl_fold] def gibbsSweep : Exp rT := pl%
  fun dimension conditional initial,
    if dimension < #0 then fail else
      let loop := (rec update index state := if dimension <= index then state else
        update (index + #1) (conditional index state));
      loop #0 initial

/-- Uniform random-scan Gibbs updates, not full sweeps. -/
@[pl_fold] def randomScanGibbs : Exp rT := pl%
  rec update dimension conditional initial steps :=
    if (dimension <= #0) || (steps < #0) then fail else
    if steps = #0 then initial else
      let index := &Occil.uniformInt dimension;
      update dimension conditional (conditional index initial) (steps - #1)

/-- Finite-grid slice-sampling transition by rejection in a known bounded domain.
The initial point has positive integer density; the slice height is an integer in
[0,density(initial)). This targets the discrete grid law proportional to density. -/
@[pl_fold] def sliceStep : Exp rT := pl%
  fun density lower upper initial,
    let height := &Occil.uniformInt (density initial);
    let proposal := (fun u, &Occil.rndIntExcRange lower upper);
    &Occil.rejection proposal (fun x, height < density x) #()

@[pl_fold] def sliceSampler : Exp rT := pl%
  rec run density lower upper initial steps :=
    if steps < #0 then fail else if steps = #0 then initial else
      run density lower upper (&sliceStep density lower upper initial) (steps - #1)

/-- Stepping-out and shrinking slice transition on an integer grid. Width and
the finite stepping-out budget are positive integers. The density callback is
defined on all integer positions and the initial point has positive density.
The random left/right budget split is retained from the stepping-out method. -/
@[pl_fold] def sliceStepOut : Exp rT := pl%
  fun density initial width maxSteps,
    if (width <= #0) || (maxSteps <= #0) then fail else
      let height := &Occil.uniformInt (density initial);
      let lower := initial - &Occil.uniformInt width;
      let upper := lower + width;
      let leftBudget := &Occil.uniformInt maxSteps;
      let rightBudget := maxSteps - #1 - leftBudget;
      let extendLeft := (rec extend boundary budget :=
        if budget = #0 then boundary else
        if height < density boundary then extend (boundary - width) (budget - #1)
        else boundary);
      let extendRight := (rec extend boundary budget :=
        if budget = #0 then boundary else
        if height < density boundary then extend (boundary + width) (budget - #1)
        else boundary);
      let left := extendLeft lower leftBudget;
      let right := extendRight upper rightBudget;
      let shrink := (rec draw lo hi :=
        let candidate := &Occil.rndIntExcRange lo hi;
        if height < density candidate then candidate else
        if candidate < initial then draw (candidate + #1) hi else draw lo candidate);
      shrink left right

@[pl_fold] def sliceSamplerStepOut : Exp rT := pl%
  rec run density initial width maxSteps steps :=
    if steps < #0 then fail else if steps = #0 then initial else
      run density (&sliceStepOut density initial width maxSteps) width maxSteps (steps - #1)

/-- A Monte Carlo permutation-test p-value as an exact (numerator,denominator)
pair. Includes the observed arrangement once, and uses independent uniform
shuffles for the requested null replicates. `statistic` returns an ordered value. -/
@[pl_fold] def permutationTest : Exp rT := pl%
  fun observations statistic replicates,
    if replicates < #0 then fail else
      let observed := statistic observations;
      let loop := (rec count remaining exceedances :=
        if remaining = #0 then (exceedances + #1, replicates + #1) else
          let shuffled := &Occil.shuffle observations;
          let value := statistic shuffled;
          count (remaining - #1) (if observed <= value then exceedances + #1 else exceedances));
      loop replicates #0

/-- An arbitrary increment law on a finite random walk; the return is the path
including the initial position. No Brownian or Gaussian scaling is implicit. -/
@[pl_fold] def randomWalkPath : Exp rT := pl%
  rec draw increment initial steps :=
    if steps < #0 then fail else
    if steps = #0 then inr((initial, inl(#()))) else
      inr((initial, draw increment (initial + increment #()) (steps - #1)))

/-! ## Random-stopped sums, extrema and episodes -/

/-- Count sampler returns a nonnegative integer. Summands may be signed grid values. -/
@[pl_fold] def stoppedSum : Exp rT := pl%
  fun countSampler sampler u,
    let count := countSampler #();
    if count < #0 then fail else
      let loop := (rec sum n := if n = #0 then #0 else sampler #() + sum (n - #1));
      loop count

@[pl_fold] def stoppedMinimum : Exp rT := pl%
  fun countSampler sampler u,
    let count := countSampler #();
    if count <= #0 then fail else
      let loop := (rec draw remaining current := if remaining = #0 then current else
        let x := sampler #();
        draw (remaining - #1) (if x < current then x else current));
      loop (count - #1) (sampler #())

@[pl_fold] def stoppedMaximum : Exp rT := pl%
  fun countSampler sampler u,
    let count := countSampler #();
    if count <= #0 then fail else
      let loop := (rec draw remaining current := if remaining = #0 then current else
        let x := sampler #();
        draw (remaining - #1) (if current < x then x else current));
      loop (count - #1) (sampler #())

/-- An episode is (sum of N samples,N), with the same sampled N in both components. -/
@[pl_fold] def episodes : Exp rT := pl%
  fun countSampler sampler u,
    let count := countSampler #();
    if count < #0 then fail else
      let loop := (rec sum n := if n = #0 then #0 else sampler #() + sum (n - #1));
      (loop count, count)

end Occil.General
