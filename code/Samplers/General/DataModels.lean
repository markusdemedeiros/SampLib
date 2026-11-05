import Samplers.General.Core
import Samplers.General.Points
import Samplers.Numerical

/-!
Finite resampling and supplied-model sampling from Occil's "Randomization in
Statistical Testing" and "Sampling from a Distribution of Data Points" sections.
Fitting a model is not a sampling algorithm and is deliberately left to the caller.
Real-valued observations, parameters and outputs below use integer fixed-point grids.
-/
namespace Occil.General
open ProbLang
variable {rT : Type _}

/-- Independent bootstrap data sets, each with the original sample size. -/
@[pl_fold] def bootstrap : Exp rT := pl%
  fun observations replicates u,
    if replicates < #0 then fail else
      let size := &Occil.length observations;
      &Occil.repeatSample (fun u, &Occil.sampleWithReplacement observations size) replicates

/-- Independently shuffled null data sets. -/
@[pl_fold] def permutationSamples : Exp rT := pl%
  fun observations replicates u,
    if replicates < #0 then fail else
      &Occil.repeatSample (fun u, &Occil.shuffle observations) replicates

/-- Split a list at an exact nonnegative position, returning (prefix,suffix). -/
@[pl_fold] def splitAt : Exp rT := pl%
  rec split xs size :=
    if size < #0 then fail else if size = #0 then (inl(#()), xs) else
      case! xs | inl(u) => fail | inr(p) =>
        let rest := split (snd(p)) (size - #1);
        (inr((fst(p), fst(rest))), snd(rest))

/-- Shuffle once and regroup without changing group sizes. The group sizes must
be nonnegative integers summing to the number of observations. -/
@[pl_fold] def groupedPermutation : Exp rT := pl%
  fun observations groupSizes u,
    if &Occil.sumInts groupSizes = &Occil.length observations then
      let shuffled := &Occil.shuffle observations;
      let partition := (rec groups xs sizes := case! sizes
        | inl(v) => inl(#())
        | inr(p) =>
          let split := &splitAt xs (fst(p));
          inr((fst(split), groups (snd(split)) (snd(p)))));
      partition shuffled groupSizes
    else fail

/-- Histogram counts are BIN MASSES, not density heights. After selecting a bin
with its observed count, select uniformly within its integer-grid interval.
Consequently unequal-width bins do not acquire an accidental width multiplier. -/
@[pl_fold] def histogram : Exp rT := pl%
  fun boundaries counts u,
    if &Occil.length boundaries = &Occil.length counts + #1 then
      let bin := &Occil.weightedChoice counts;
      let lower := &Occil.getAt boundaries bin;
      let upper := &Occil.getAt boundaries (bin + #1);
      &Occil.rndIntExcRange lower upper
    else fail

/-- A supplied Gaussian mixture: components are (mean,standardDeviation) pairs,
weights are nonnegative integer mixture masses. This does not fit the mixture. -/
@[pl_fold] def gaussianMixture : Exp rT := pl%
  fun scale weights components u,
    if &Occil.length weights = &Occil.length components then
      let index := &Occil.weightedChoice weights;
      let parameters := &Occil.getAt components index;
      &Numerical.normal scale (fst(parameters)) (snd(parameters)) #()
    else fail

/-- Scalar kernel-density sampling: an empirical center plus fresh kernel jitter.
`jitter unit` returns an offset in the same integer grid as the observations. -/
@[pl_fold] def kernelDensity : Exp rT := pl%
  fun observations jitter u,
    let center := &Occil.choice observations;
    center + jitter #()

/-- Vector KDE with an independent scalar jitter per coordinate. Dependence
between center coordinates is retained by choosing ONE observation vector. -/
@[pl_fold] def kernelDensityVector : Exp rT := pl%
  fun observations jitter u,
    let center := &Occil.choice observations;
    &map (fun x, x + jitter #()) center

@[pl_fold] def gaussianKernelDensity : Exp rT := pl%
  fun scale observations bandwidth u,
    &kernelDensity observations (fun u, &Numerical.normal scale #0 bandwidth #()) #()

@[pl_fold] def gaussianKernelDensityVector : Exp rT := pl%
  fun scale observations bandwidth u,
    &kernelDensityVector observations (fun u, &Numerical.normal scale #0 bandwidth #()) #()

/-- A fitted linear-regression prediction with Gaussian residual error. Coefficients
and inputs are fixed-point lists of equal length; intercept and nonnegative MSE
share the same scale. A zero residual variance produces the deterministic mean. -/
@[pl_fold] def linearRegression : Exp rT := pl%
  fun scale coefficients intercept mse inputs u,
    if mse < #0 then fail else
      let dot := (rec sum cs xs := case! cs
        | inl(v) => case! xs | inl(w) => #0 | inr(p) => fail
        | inr(p) => case! xs | inl(w) => fail | inr(q) =>
            &Numeric.mul scale (fst(p)) (fst(q)) + sum (snd(p)) (snd(q)));
      let mean := intercept + dot coefficients inputs;
      if mse = #0 then mean else
        mean + &Numerical.normal scale #0 (&Numeric.sqrt scale mse) #()

/-- Decode one independently sampled latent value through a supplied deterministic
fitted generative model. No training or target-distribution oracle is hidden here. -/
@[pl_fold] def generativeModel : Exp rT := pl%
  fun latentSampler decoder u,
    let latent := latentSampler #();
    decoder latent

/-- Mixture over class-conditional fitted models. Returns (classIndex,observation).
Each entry of modelSamplers is a unit-taking object-language sampler. -/
@[pl_fold] def classifiedModel : Exp rT := pl%
  fun classCounts modelSamplers u,
    if &Occil.length classCounts = &Occil.length modelSamplers then
      let category := &Occil.weightedChoice classCounts;
      let sampler := &Occil.getAt modelSamplers category;
      (category, sampler #())
    else fail

/-! ## Stochastic interpolation (Saucier §5.3.4)

The cited Army Research Laboratory report ARL-TR-2168 specifies normalized
nearest-neighbor interpolation with one shared random weight per neighbor vector.
The output need not stay inside the original bounding box. Constant coordinate
axes are retained exactly instead of dividing by their zero range.
-/

@[pl_fold] def vectorZipWith : Exp rT := pl%
  rec combine operation left right := case! left
    | inl(u) => case! right | inl(v) => inl(#()) | inr(p) => fail
    | inr(p) => case! right | inl(v) => fail | inr(q) =>
        inr((operation (fst(p)) (fst(q)), combine operation (snd(p)) (snd(q))))

@[pl_fold] def dataBounds : Exp rT := pl%
  fun observations,
    let dimension := &Occil.length (&Occil.getAt observations #0);
    let build := (rec coordinate index := if index = dimension then inl(#()) else
      let initial := &Occil.getAt (&Occil.getAt observations #0) index;
      let scan := (rec bounds points lower upper := case! points
        | inl(u) => (lower, upper)
        | inr(p) =>
          let x := &Occil.getAt (fst(p)) index;
          bounds (snd(p)) (if x < lower then x else lower) (if upper < x then x else upper));
      inr((scan observations initial initial, coordinate (index + #1))));
    build #0

@[pl_fold] def normalizeDataPoint : Exp rT := pl%
  rec normalize scale bounds point := case! bounds
    | inl(u) => case! point | inl(v) => inl(#()) | inr(p) => fail
    | inr(p) => case! point | inl(v) => fail | inr(q) =>
        let interval := fst(p);
        let width := snd(interval) - fst(interval);
        if width < #0 then fail else
          let x := (if width = #0 then #0 else
            &Numeric.div scale (fst(q) - fst(interval)) width);
          inr((x, normalize scale (snd(p)) (snd(q))))

@[pl_fold] def denormalizeDataPoint : Exp rT := pl%
  rec restore scale bounds point := case! bounds
    | inl(u) => case! point | inl(v) => inl(#()) | inr(p) => fail
    | inr(p) => case! point | inl(v) => fail | inr(q) =>
        let interval := fst(p);
        let x := fst(interval) + &Numeric.mul scale (fst(q)) (snd(interval) - fst(interval));
        inr((x, restore scale (snd(p)) (snd(q))))

/-- Saucier's nearest-neighbor stochastic interpolation. `neighborhood` includes
the randomly selected center and must lie in 1..numberOfObservations. For m=1,
this is exactly empirical resampling. All arithmetic is fixed-point numerical. -/
@[pl_fold] def stochasticInterpolation : Exp rT := pl%
  fun scale observations neighborhood u,
    if (scale <= #1) || (neighborhood <= #0) || (&Occil.length observations < neighborhood) then fail else
    if neighborhood = #1 then &Occil.choice observations else
      let bounds := &dataBounds observations;
      let normalized := &map (fun point, &normalizeDataPoint scale bounds point) observations;
      let origin := &Occil.choice normalized;
      let insert := (rec ordered point points := case! points
        | inl(v) => inr((point, inl(#())))
        | inr(p) =>
          if &squaredDistance point origin <= &squaredDistance (fst(p)) origin then
            inr((point, points))
          else inr((fst(p), ordered point (snd(p)))));
      let sorted := &fold (fun acc point, insert point acc) (inl(#())) normalized;
      let nearest := fst(&splitAt sorted neighborhood);
      let first := &Occil.getAt nearest #0;
      let zeros := &map (fun x, #0) first;
      let total := &fold (fun acc point, &vectorZipWith (fun x y, x + y) acc point) zeros nearest;
      let mean := &map (fun x, x / neighborhood) total;
      let spread := &Numeric.sqrt scale (#3 * scale * (neighborhood - #1));
      let lower := (scale - spread) / neighborhood;
      let upper := (scale + spread) / neighborhood;
      let perturb := (fun point,
        let weight := &Occil.rndIntExcRange lower upper;
        &vectorZipWith (fun x center, &Numeric.mul scale (x - center) weight) point mean);
      let offset := &fold (fun acc point, &vectorZipWith (fun x y, x + y) acc (perturb point)) zeros nearest;
      let result := &vectorZipWith (fun x delta, x + delta) mean offset;
      &denormalizeDataPoint scale bounds result

end Occil.General
