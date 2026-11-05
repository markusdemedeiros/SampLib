import Samplers.Weighted.Core
import Samplers.Discrete

/-! # Cumulative tables and rational weights

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Prefix preprocessing and categorical search. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- Prefix sums, with validation; returns (total,cumulative list). -/
@[pl_fold] def cumulativeTable : Exp rT := pl%
  fun weights,
    if &validWeights weights then
      let scan := (rec build xs running := case! xs
        | inl(u) => inl(#())
        | inr(p) =>
          let next := running + fst(p);
          inr((next, build (snd(p)) next)));
      (&Occil.sumInts weights, scan weights #0)
    else fail

/-- Binary search for the first cumulative weight strictly above a uniform ticket.
List indexing is linear; the number of cumulative comparisons is logarithmic. -/
@[pl_fold] def cumulativeDraw : Exp rT := pl%
  fun table u,
    let total := fst(table);
    let cumulative := snd(table);
    let ticket := &Occil.uniformInt total;
    let search := (rec bisect low high :=
      if high <= low then low else
        let middle := (low + high) / #2;
        if ticket < &Occil.getAt cumulative middle then bisect low middle
        else bisect (middle + #1) high);
    search #0 (&Occil.length cumulative - #1)

@[pl_fold] def cumulativeChoice : Exp rT := pl%
  fun weights u, &cumulativeDraw (&cumulativeTable weights) #()

/-! ## Exact normalization of rational weights. -/
/-- Normalize rational weights (numerator,positive denominator) to integers.
Uses their product denominator, avoiding any floating-point conversion. -/
@[pl_fold] def rationalWeights : Exp rT := pl%
  fun weights,
    let denominator := (rec product xs := case! xs
      | inl(u) => #1
      | inr(p) =>
          let fraction := fst(p);
          if ((fst(fraction)) < #0) || ((snd(fraction)) <= #0) then fail else
            (snd(fraction)) * product (snd(p)));
    let common := denominator weights;
    let normalize := (rec convert xs := case! xs
      | inl(u) => inl(#())
      | inr(p) =>
          let fraction := fst(p);
          inr(((fst(fraction)) * (common / snd(fraction)), convert (snd(p)))));
    normalize weights

@[pl_fold] def rationalChoice : Exp rT := pl%
  fun weights u, &Occil.weightedChoice (&rationalWeights weights)

end Occil.Weighted
