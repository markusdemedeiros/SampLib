import Samplers.Weighted.Core

/-! # Weighted reservoirs and prescribed inclusion probabilities

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## One-item weighted reservoir. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- One-item weighted reservoir. Each arriving item replaces the reservoir with
probability weight/(running total); requires nonnegative integer weights. -/
@[pl_fold] def weightedReservoirOne : Exp rT := pl%
  fun weights u,
    if &validWeights weights then
      let scan := (rec visit xs total selected index := case! xs
        | inl(v) => selected
        | inr(p) =>
            let next := total + fst(p);
            if next = #0 then visit (snd(p)) next selected (index + #1) else
              if &Occil.rationalCoin (fst(p)) next then
                visit (snd(p)) next index (index + #1)
              else visit (snd(p)) next selected (index + #1));
      scan weights #0 #(-1) #0
    else fail

/-! ## Fixed-size unequal-probability sampling. -/
/-- Insert a (probability numerator,label) pair into ascending probability order. -/
@[pl_fold] def insertProbability : Exp rT := pl%
  rec insert item items := case! items
    | inl(u) => inr((item, inl(#())))
    | inr(p) =>
        let first := fst(p);
        if (fst(item)) <= (fst(first)) then inr((item, items))
        else inr((first, insert item (snd(p))))

/-- Fixed-size unequal-probability sampling by Deville–Tillé splitting.
Every inclusion probability is count*weight/total and must be <=1. The common
probability denominator is updated exactly after each rejected splitting step. -/
@[pl_fold] def inclusionSplitting : Exp rT := pl%
  fun weights count,
    let n := &Occil.length weights;
    if (count < #0) || (n < count) then fail else
    if count = #0 then inl(#()) else
    if &validWeights weights then
      let total := &Occil.sumInts weights;
      let prepare := (rec build xs label := case! xs
        | inl(u) => inl(#())
        | inr(p) =>
            let numerator := count * fst(p);
            if total < numerator then fail else
              &insertProbability (numerator, label) (build (snd(p)) (label + #1)));
      let select := (rec take xs remaining := case! xs
        | inl(u) => inl(#())
        | inr(p) =>
            let item := fst(p);
            if #0 < remaining then take (snd(p)) (remaining - #1)
            else inr((snd(item), take (snd(p)) #0)));
      if count = n then select (prepare weights #0) #0 else
        let loop := (rec split items denominator :=
          let lowBoundary := &Occil.getAt items (n - count - #1);
          let highBoundary := &Occil.getAt items (n - count);
          let complement := denominator - fst(lowBoundary);
          let high := fst(highBoundary);
          let lambda := (if complement < high then complement else high);
          if lambda <= #0 then fail else
          if &Occil.rationalCoin lambda denominator then select items (n - count) else
            let adjust := (rec update xs remaining := case! xs
              | inl(u) => inl(#())
              | inr(p) =>
                  let item := fst(p);
                  let numerator := (if #0 < remaining then fst(item) else fst(item) - lambda);
                  let rest := update (snd(p)) (remaining - #1);
                  &insertProbability (numerator, snd(item)) rest);
            split (adjust items (n - count)) (denominator - lambda));
        loop (prepare weights #0) total
    else fail

/-- Systematic PPS sample with the same prescribed inclusion probabilities.
One uniformly shifted lattice gives exactly count selected indices; its joint
law differs from Deville–Tillé splitting and from sequential PPS selection. -/
@[pl_fold] def inclusionSystematic : Exp rT := pl%
  fun weights count,
    if (count < #0) || (&Occil.length weights < count) then fail else
    if count = #0 then inl(#()) else
    if &validWeights weights then
      let total := &Occil.sumInts weights;
      let ticket := &Occil.uniformInt total;
      let scan := (rec select xs before label := case! xs
        | inl(u) => inl(#())
        | inr(p) =>
            let width := count * fst(p);
            if total < width then fail else
              let after := before + width;
              if (before + ticket) / total < (after + ticket) / total then
                inr((label, select (snd(p)) after (label + #1)))
              else select (snd(p)) after (label + #1));
      scan weights #0 #0
    else fail

end Occil.Weighted
