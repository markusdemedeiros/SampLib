import Samplers.Discrete

/-! Integer-weight rejection, sequential selection, and alias preprocessing. -/
namespace Occil

open ProbLang

variable {rT : Type _}

/-- Categorical rejection using an integer envelope. Each proposal is uniform
over indices, accepted with weight[index]/envelope; all weights <= envelope. -/
@[pl_fold] def weightedRejection : Exp rT := pl%
  fun weights envelope,
    let valid := (rec check xs := case! xs | inl(u) => #true | inr(p) =>
      if (fst(p) < #0) || (envelope < fst(p)) then #false else check (snd(p)));
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
      (if #0 < fst(p) then #1 else #0) + count (snd(p)));
    let setZero := (rec update xs i := case! xs | inl(u) => fail | inr(p) =>
      if i = #0 then inr((#0, snd(p))) else
        inr((fst(p), update (snd(p)) (i - #1))));
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
      if fst(p) < #0 then #false else check (snd(p)));
    if (n <= #0) || (total <= #0) || (count < #0) then fail else
    if valid weights then
      let work := allocN(n, #0);
      let thresholds := allocN(n, total);
      let aliases := allocN(n, #0);
      let setupArray := (rec fill xs i := case! xs | inl(u) => #() | inr(p) =>
        ((work +ₗ i) ← (n * fst(p));
         (aliases +ₗ i) ← i;
         fill (snd(p)) (i + #1)));
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
            let smallWeight := !(work +ₗ small);
            let largeWeight := !(work +ₗ large);
            (thresholds +ₗ small) ← smallWeight;
            (aliases +ₗ small) ← large;
            (work +ₗ large) ← (largeWeight + smallWeight - total);
            (work +ₗ small) ← total;
            balance #());
      prepare #();
      let draw := (fun u,
        let i := &uniformInt n;
        if &uniformInt total < !(thresholds +ₗ i) then i else !(aliases +ₗ i));
      &repeatSample draw count
    else fail

end Occil
