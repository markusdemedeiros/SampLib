import Samplers.Combinatorial
import Samplers.Continuous

/-! Additional algorithms from randomgen.py, bernoulli.py and randmisc.html.
Comments distinguish direct translations from simple distributional constructions. -/
namespace Occil
open ProbLang
variable {rT : Type _}

/-- Bounded failures before success (the direct trial variant). Unlike capping
an unbounded geometric, this also terminates when p=0. -/
@[pl_fold] def boundedGeometric : Exp rT := pl%
  rec draw coin bound := if bound < #0 then fail else if bound = #0 then #0 else
    if coin #() then #0 else #1 + draw coin (bound - #1)

/-- Generic rejection: requires positive acceptance probability and fresh proposals. -/
@[pl_fold] def rejection : Exp rT := pl%
  rec draw proposal accept u :=
    let x := proposal #();
    if accept x then x else draw proposal accept #()

/-- Rational scaled logistic factory cp/(1+cp), c=x/y>0. -/
@[pl_fold] def logisticFactory : Exp rT := pl%
  rec draw coin x y u :=
    if (x <= #0) || (y <= #0) then fail else
      if &rationalCoin y (x + y) then #false else
      if coin #() then #true else draw coin x y #()

/-- Probability generating function E[p^N] for a nonnegative integer sampler. -/
@[pl_fold] def probabilityGeneratingFactory : Exp rT := pl%
  fun coin integerSampler u,
    let n := integerSampler #();
    if n < #0 then fail else &iterateCoin coin n

/-- Polynomial in Bernstein form: flip n times, then select coefficient #heads.
Coefficients are rational (numerator,denominator) pairs. -/
@[pl_fold] def bernsteinFactory : Exp rT := pl%
  fun coin coefficients u,
    let n := &length coefficients - #1;
    if n < #0 then fail else
      let heads := &binomial coin n;
      let coefficient := &getAt coefficients heads;
      &rationalCoin ((fst(coefficient))) ((snd(coefficient)))

/-- Categorical rejection using an integer envelope. Each proposal is uniform
over indices, accepted with weight[index]/envelope; all weights <= envelope. -/
@[pl_fold] def weightedRejection : Exp rT := pl%
  fun weights envelope,
    let valid := (rec check xs := case! xs | inl(u) => #true | inr(p) =>
      if (((fst(p))) < #0) || (envelope < ((fst(p)))) then #false else check ((snd(p))));
    if (envelope <= #0) || (&sumInts weights <= #0) then fail else
    if valid weights then
      let loop := (rec draw u :=
        let i := &uniformInt (&length weights);
        if &rationalCoin (&getAt weights i) envelope then i else draw #());
      loop #()
    else fail

/-- Sequential probability-proportional-to-size sampling without replacement.
Return category indices. Zero weights are never selected. -/
@[pl_fold] def weightedWithoutReplacement : Exp rT := pl%
  fun weights k,
    let positive := (rec count xs := case! xs | inl(u) => #0 | inr(p) =>
      (if #0 < ((fst(p))) then #1 else #0) + count ((snd(p))));
    let setZero := (rec update xs i := case! xs | inl(u) => fail | inr(p) =>
      if i = #0 then inr((#0, (snd(p)))) else
        inr(((fst(p)), update ((snd(p))) (i - #1))));
    if (k < #0) || (positive weights < k) then fail else
      let loop := (rec draw ws remaining := if remaining = #0 then inl(#()) else
        let i := &weightedChoice ws;
        inr((i, draw (setZero ws i) (remaining - #1))));
      loop weights k

/-- Exact Walker alias preprocessing and draws with integer thresholds. Return
`count` independent indices. Preprocessing is object-language heap manipulation;
the O(n^2) scan avoids depending on a separate queue/list implementation. -/
@[pl_fold] def aliasSamples : Exp rT := pl%
  fun weights count,
    let n := &length weights;
    let total := &sumInts weights;
    let valid := (rec check xs := case! xs | inl(u) => #true | inr(p) =>
      if ((fst(p))) < #0 then #false else check ((snd(p))));
    if (n <= #0) || (total <= #0) || (count < #0) then fail else
    if valid weights then
      let work := allocN(n, #0);
      let thresholds := allocN(n, total);
      let aliases := allocN(n, #0);
      let setupArray := (rec fill xs i := case! xs | inl(u) => #() | inr(p) =>
        ((work +ₗ i) ← (n * (fst(p)));
         (aliases +ₗ i) ← i;
         fill ((snd(p))) (i + #1)));
      setupArray weights #0;
      let find := (rec scan i low := if i = n then #(-1) else
        let w := !(work +ₗ i);
        if low then if w < total then i else scan (i + #1) low
        else if total < w then i else scan (i + #1) low);
      let prepare := (rec balance u :=
        let small := find #0 #true;
        if small < #0 then #() else
          let large := find #0 #false;
          if large < #0 then fail else
            let a := !(work +ₗ small);
            let b := !(work +ₗ large);
            (thresholds +ₗ small) ← a;
            (aliases +ₗ small) ← large;
            (work +ₗ large) ← (b + a - total);
            (work +ₗ small) ← total;
            balance #());
      prepare #();
      let draw := (fun u,
        let i := &uniformInt n;
        if &uniformInt total < !(thresholds +ₗ i) then i else !(aliases +ₗ i));
      &repeatSample draw count
    else fail

/-- Sattolo's uniform single-cycle permutation (NOT a uniform derangement). -/
@[pl_fold] def sattolo : Exp rT := pl%
  fun xs,
    let n := &length xs;
    if n = #0 then inl(#()) else
      let a := allocN(n, #());
      &fillArray a xs #0;
      let loop := (rec swap i := if i <= #0 then #() else
        let j := &uniformInt i;
        let x := !(a +ₗ i);
        let y := !(a +ₗ j);
        (a +ₗ i) ← y;
        (a +ₗ j) ← x;
        swap (i - #1));
      loop (n - #1);
      &readArray a #0 n

/-- Uniform derangement of positions 0..n-1 by rejection from a full shuffle.
The simple rejection construction differs from randomgen.py's optimized _shufflemod. -/
@[pl_fold] def derangement : Exp rT := pl%
  fun n,
    if (n < #0) || (n = #1) then fail else
      let fixedPointFree := (rec check xs i := case! xs
        | inl(u) => #true | inr(p) =>
          if ((fst(p))) = i then #false else check ((snd(p))) (i + #1));
      &rejection (fun u, &shuffle (&intRange #0 n)) (fun xs, fixedPointFree xs #0) #()

/-- Randomly flip each bit independently according to an abstract coin. -/
@[pl_fold] def flipBits : Exp rT := pl%
  rec flip xs coin := case! xs | inl(u) => inl(#()) | inr(p) =>
    let bit := (if coin #() then ~((fst(p))) else (fst(p)));
    inr((bit, flip ((snd(p))) coin))

end Occil
