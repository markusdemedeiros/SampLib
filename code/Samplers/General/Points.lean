import Samplers.General.Core
import Samplers.Numeric

/-!
Point-set generators listed under Occil's "Point Sample Selection". All outputs
are integer coordinates on [0,scale); divide by scale to obtain numerical points.
Deterministic low-discrepancy generators are deliberately distinguished from iid
sampling. Direction numbers, digit permutations and feedback masks are data, not
probability oracles. Finite-grid quantization can introduce collisions and periods.
-/
namespace Occil.General
open ProbLang
variable {rT : Type _}

@[pl_fold] def integerPower : Exp rT := pl%
  fun base exponent,
    if exponent < #0 then fail else
      let loop := (rec power n acc := if n = #0 then acc else power (n - #1) (acc * base));
      loop exponent #1

/-- Base-b radical inverse as an exact numerator/denominator pair. -/
@[pl_fold] def vanDerCorputRational : Exp rT := pl%
  fun base index,
    if (base < #2) || (index < #0) then fail else
      let loop := (rec reverseDigits n numerator denominator :=
        if n = #0 then (numerator, denominator) else
          reverseDigits (n / base) (numerator * base + n % base) (denominator * base));
      loop index #0 #1

@[pl_fold] def vanDerCorput : Exp rT := pl%
  fun scale base index,
    if scale <= #0 then fail else
      let fraction := &vanDerCorputRational base index;
      scale * fst(fraction) / snd(fraction)

/-- A Halton point; bases should be distinct primes for the usual discrepancy
properties. The generator itself accepts any list of bases at least two. -/
@[pl_fold] def halton : Exp rT := pl%
  fun scale bases index,
    &map (fun base, &vanDerCorput scale base index) bases

/-- Fixed-length digit scrambling of a radical inverse. `permutations` contains
one permutation of 0..base-1 per digit position, including padded zero digits. -/
@[pl_fold] def scrambledRadicalInverse : Exp rT := pl%
  fun scale base index permutations,
    if (scale <= #0) || (base < #2) || (index < #0) then fail else
      let loop := (rec scramble n tables numerator denominator := case! tables
        | inl(u) => scale * numerator / denominator
        | inr(p) =>
          let digit := &Occil.getAt (fst(p)) (n % base);
          if (digit < #0) || (base <= digit) then fail else
            scramble (n / base) (snd(p)) (numerator * base + digit) (denominator * base));
      loop index permutations #0 #1

/-- A shared random shift may randomize an entire low-discrepancy point set.
Pass the SAME shift vector to every point, rather than drawing a shift per point. -/
@[pl_fold] def shiftPoint : Exp rT := pl%
  rec shift scale point offsets := case! point
    | inl(u) => case! offsets | inl(v) => inl(#()) | inr(p) => fail
    | inr(p) => case! offsets
      | inl(v) => fail
      | inr(q) => if scale <= #0 then fail else
          inr(((fst(p) + fst(q)) % scale, shift scale (snd(p)) (snd(q))))

/-- Baker's tent map, 2*min(x,1-x), on the fixed grid. -/
@[pl_fold] def bakersMap : Exp rT := pl%
  fun scale x,
    if (scale <= #0) || (x < #0) || (scale < x) then fail else
      scale - &Numeric.abs (#2 * x - scale)

/-- Root of phi^(dimension+1)=phi+1, found numerically on [1,2]. -/
@[pl_fold] def generalizedGoldenRatio : Exp rT := pl%
  fun scale dimension,
    if (scale <= #1) || (dimension <= #0) then fail else
      let power := (rec multiply x remaining acc :=
        if remaining = #0 then acc else
          multiply x (remaining - #1) (&Numeric.mul scale acc x));
      let bisect := (rec solve lower upper :=
        if upper - lower <= #1 then upper else
          let mid := (lower + upper) / #2;
          if power mid (dimension + #1) scale < mid + scale then solve mid upper
          else solve lower mid);
      bisect scale (#2 * scale)

/-- Roberts R_d sequence, with seed 1/2 and alpha_j=phi^(-j). This is an
explicit fixed-precision approximation of the irrational additive recurrence. -/
@[pl_fold] def robertsPoint : Exp rT := pl%
  fun scale dimension index,
    if index < #0 then fail else
      let phi := &generalizedGoldenRatio scale dimension;
      let build := (rec coordinate remaining alpha :=
        if remaining = #0 then inl(#()) else
          let next := &Numeric.div scale alpha phi;
          inr(((scale / #2 + index * next) % scale, coordinate (remaining - #1) next)));
      build dimension scale

/-- Bitwise exclusive-or for nonnegative integers, expressed with arithmetic. -/
@[pl_fold] def bitXor : Exp rT := pl%
  fun left right,
    if (left < #0) || (right < #0) then fail else
      let loop := (rec combine a b place acc :=
        if (a = #0) && (b = #0) then acc else
          let digit := (if a % #2 = b % #2 then #0 else place);
          combine (a / #2) (b / #2) (place * #2) (acc + digit));
      loop left right #1 #0

/-- A Sobol coordinate in Gray-code order from its finite direction-number row.
Direction integers are scaled by 2^bits, and the row must have exactly bits entries.
The caller supplies valid primitive-polynomial direction data for each dimension. -/
@[pl_fold] def sobolCoordinate : Exp rT := pl%
  fun scale bits directions index,
    let denominator := &integerPower #2 bits;
    if (scale <= #0) || (bits <= #0) || (index < #0) || (denominator <= index) then fail else
    if &Occil.length directions = bits then
      let loop := (rec accumulate n row acc := case! row
        | inl(u) => scale * acc / denominator
        | inr(p) =>
          let direction := fst(p);
          if (direction < #0) || (denominator <= direction) then fail else
            let next := (if n % #2 = (n / #2) % #2 then acc else &bitXor acc direction);
            accumulate (n / #2) (snd(p)) next);
      loop index directions #0
    else fail

@[pl_fold] def sobolPoint : Exp rT := pl%
  fun scale bits directionRows index,
    &map (fun row, &sobolCoordinate scale bits row index) directionRows

/-- Self-contained first two Sobol dimensions: first row binary-place values;
second row the degree-one primitive-polynomial recurrence v <- v xor (v/2).
Higher dimensions use `sobolPoint` with the published direction-number data. -/
@[pl_fold] def sobol2 : Exp rT := pl%
  fun scale bits index,
    let denominator := &integerPower #2 bits;
    let first := (rec row remaining value :=
      if remaining = #0 then inl(#()) else inr((value, row (remaining - #1) (value / #2))));
    let second := (rec row remaining value :=
      if remaining = #0 then inl(#()) else
        inr((value, row (remaining - #1) (&bitXor value (value / #2)))));
    &sobolPoint scale bits (inr((first bits (denominator / #2),
      inr((second bits (denominator / #2), inl(#())))))) index

/-- One-dimensional stratification: one uniform grid point per equal continuous
stratum, with endpoints rounded down. Requires 1<=strata<=scale. -/
@[pl_fold] def stratified1D : Exp rT := pl%
  fun scale strata u,
    if (strata <= #0) || (scale < strata) then fail else
      let build := (rec draw index := if index = strata then inl(#()) else
        let lower := index * scale / strata;
        let upper := (index + #1) * scale / strata;
        inr((&Occil.rndIntExcRange lower upper, draw (index + #1))));
      build #0

/-- The source's shuffled stratified one-dimensional Latin-hypercube sequence. -/
@[pl_fold] def latinHypercube1D : Exp rT := pl%
  fun scale strata u, &Occil.shuffle (&stratified1D scale strata #())

/-- n points in d dimensions, with an independent shuffled stratification in
EVERY coordinate. Consequently each marginal visits each stratum exactly once. -/
@[pl_fold] def latinHypercube : Exp rT := pl%
  fun scale count dimension u,
    if dimension <= #0 then fail else
      let columns := &Occil.repeatSample (fun u, &latinHypercube1D scale count #()) dimension;
      let rows := (rec build index := if index = count then inl(#()) else
        inr((&map (fun column, &Occil.getAt column index) columns, build (index + #1))));
      rows #0

/-- One jittered point from the cell whose base-bins digits give its coordinate
indices. This helper is deterministic in the cell index and random in its jitter. -/
@[pl_fold] def stratifiedCell : Exp rT := pl%
  fun scale bins dimension cell,
    if (bins <= #0) || (scale < bins) || (dimension <= #0) || (cell < #0) then fail else
      let build := (rec coordinate remaining index := if remaining = #0 then inl(#()) else
        let digit := index % bins;
        let lower := digit * scale / bins;
        let upper := (digit + #1) * scale / bins;
        inr((&Occil.rndIntExcRange lower upper, coordinate (remaining - #1) (index / bins))));
      if cell < &integerPower bins dimension then build dimension cell else fail

/-- Jittered Cartesian stratification: perCell independent points in each of
bins^dimension cells. Returns a flat point list in cell order. -/
@[pl_fold] def stratifiedBox : Exp rT := pl%
  fun scale bins dimension perCell u,
    if (bins <= #0) || (scale < bins) || (dimension <= #0) || (perCell < #0) then fail else
      let cells := &integerPower bins dimension;
      let build := (rec draw cell := if cell = cells then inl(#()) else
        &append (&Occil.repeatSample (fun u, &stratifiedCell scale bins dimension cell) perCell)
          (draw (cell + #1)));
      build #0

/-- The concrete MLCG lattice example in Occil's point-selection section.
Coordinates are MLCG(index+j), with multiplier 92717 and modulus 262139. -/
@[pl_fold] def latticePoint : Exp rT := pl%
  fun scale dimension index,
    if (scale <= #0) || (dimension <= #0) || (index < #0) then fail else
      let build := (rec coordinate j := if j = dimension then inl(#()) else
        inr((scale * ((#92717 * (index + j)) % #262139) / #262139,
          coordinate (j + #1))));
      build #0

/-- A binary right-shifting LFSR step. `tapMask` selects feedback bits;
primitive masks and nonzero seeds are required for maximal-period applications. -/
@[pl_fold] def lfsrStep : Exp rT := pl%
  fun bits tapMask state,
    let bound := &integerPower #2 bits;
    if (bits <= #0) || (tapMask <= #0) || (bound <= tapMask) || (state <= #0) || (bound <= state) then fail else
      let parity := (rec count a b acc :=
        if (a = #0) || (b = #0) then acc % #2 else
          count (a / #2) (b / #2) (acc + (a % #2) * (b % #2)));
      state / #2 + parity state tapMask #0 * (bound / #2)

/-- Consecutive LFSR states as a numerical point. Returns (point,nextState). -/
@[pl_fold] def lfsrPoint : Exp rT := pl%
  fun scale bits tapMask dimension state,
    if (scale <= #0) || (dimension <= #0) then fail else
      let bound := &integerPower #2 bits;
      let build := (rec coordinate remaining current :=
        if remaining = #0 then (inl(#()), current) else
          let next := &lfsrStep bits tapMask current;
          let rest := coordinate (remaining - #1) next;
          (inr((scale * current / bound, fst(rest))), snd(rest)));
      build dimension state

/-! ## Geometric separation point sets -/

@[pl_fold] def uniformBoxPoint : Exp rT := pl%
  rec draw scale dimension :=
    if (scale <= #0) || (dimension < #0) then fail else
    if dimension = #0 then inl(#()) else
      inr((&Occil.uniformInt scale, draw scale (dimension - #1)))

@[pl_fold] def squaredDistance : Exp rT := pl%
  rec distance left right := case! left
    | inl(u) => case! right | inl(v) => #0 | inr(p) => fail
    | inr(p) => case! right
      | inl(v) => fail
      | inr(q) =>
        let delta := fst(p) - fst(q);
        delta * delta + distance (snd(p)) (snd(q))

/-- Minimum squared Euclidean distance to a nonempty list of points. -/
@[pl_fold] def nearestSquaredDistance : Exp rT := pl%
  fun point points,
    case! points | inl(u) => fail | inr(p) =>
      let initial := &squaredDistance point (fst(p));
      let scan := (rec minimum xs best := case! xs
        | inl(u) => best
        | inr(q) =>
          let value := &squaredDistance point (fst(q));
          minimum (snd(q)) (if value < best then value else best));
      scan (snd(p)) initial

/-- Best-candidate point selection. Each iteration picks the most separated of
`candidates` new iid proposals; this is not iid uniform sampling of point sets. -/
@[pl_fold] def bestCandidate : Exp rT := pl%
  fun scale dimension candidates count u,
    if (scale <= #0) || (dimension <= #0) || (candidates <= #0) || (count < #0) then fail else
    if count = #0 then inl(#()) else
      let first := &uniformBoxPoint scale dimension;
      let build := (rec draw remaining points := if remaining = #0 then points else
        let initial := &uniformBoxPoint scale dimension;
        let choose := (rec improve n best score :=
          if n = #0 then best else
            let candidate := &uniformBoxPoint scale dimension;
            let distance := &nearestSquaredDistance candidate points;
            if score < distance then improve (n - #1) candidate distance
            else improve (n - #1) best score);
        let selected := choose (candidates - #1) initial (&nearestSquaredDistance initial points);
        draw (remaining - #1) (&append points (inr((selected, inl(#()))))));
      build (count - #1) (inr((first, inl(#()))))

/-- Greedy farthest-point traversal of a finite candidate pool. The initial
position is selected uniformly; subsequent positions maximize nearest distance.
Selected pool positions are removed even if finite-grid coordinates coincide. -/
@[pl_fold] def farthestPoints : Exp rT := pl%
  fun pool count u,
    if (count < #0) || (&Occil.length pool < count) then fail else
    if count = #0 then inl(#()) else
      let start := &Occil.removeAt pool (&Occil.uniformInt (&Occil.length pool));
      let build := (rec draw remaining candidates selected := if remaining = #0 then selected else
        let initial := &Occil.getAt candidates #0;
        let best := (rec scan index bestIndex bestDistance :=
          if &Occil.length candidates <= index then bestIndex else
            let point := &Occil.getAt candidates index;
            let distance := &nearestSquaredDistance point selected;
            if bestDistance < distance then scan (index + #1) index distance
            else scan (index + #1) bestIndex bestDistance);
        let index := best #1 #0 (&nearestSquaredDistance initial selected);
        let chosen := &Occil.removeAt candidates index;
        draw (remaining - #1) (snd(chosen)) (&append selected (inr((fst(chosen), inl(#()))))));
      build (count - #1) (snd(start)) (inr((fst(start), inl(#()))))

/-- Random sequential hard-core (Poisson-disk) rejection on a finite grid.
Returns (acceptedPoints,complete). A finite trial budget can return a short set;
it never silently claims that a jammed configuration reached the requested size. -/
@[pl_fold] def poissonDiskRejection : Exp rT := pl%
  fun scale dimension separation count trials u,
    if (scale <= #0) || (dimension <= #0) || (separation < #0) || (count < #0) || (trials < #0) then fail else
      let separated := (rec check candidate points := case! points
        | inl(v) => #true
        | inr(p) => if &squaredDistance candidate (fst(p)) < separation * separation then #false
          else check candidate (snd(p)));
      let build := (rec draw remaining budget points :=
        if remaining = #0 then (points, #true) else
        if budget = #0 then (points, #false) else
          let candidate := &uniformBoxPoint scale dimension;
          if separated candidate points then
            draw (remaining - #1) (budget - #1) (&append points (inr((candidate, inl(#())))))
          else draw remaining (budget - #1) points);
      build count trials (inl(#()))

end Occil.General
