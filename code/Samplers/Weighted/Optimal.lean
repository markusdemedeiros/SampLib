import Samplers.Weighted.Core

/-! # Finite cyclic probability matrices

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Saad probability-matrix preprocessing and traversal. -/
namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Saad's finite cyclic binary probability matrix, with a rejection outcome
when the requested weight sum is not 2^k-2^l. Returns (matrix,(k,(l,rejectIndex))). -/
@[pl_fold] def optimalMatrix : Exp rT := pl%
  fun weights,
    if &Weighted.validWeights weights then
      let total := &Occil.sumInts weights;
      let k := &bitLength total;
      let ceiling := &Weighted.integerPower #2 k;
      let parameters := (rec select l bestL bestTotal :=
        if k <= l then (bestL, bestTotal) else
          let denominator := ceiling - &Weighted.integerPower #2 l;
          if denominator = total then (l, denominator) else
          if denominator < total then (bestL, bestTotal)
          else select (l + #1) l denominator);
      let selected := parameters #0 k ceiling;
      let l := (fst(selected));
      let denominator := (snd(selected));
      let rejected := denominator - total;
      let values := (if rejected = #0 then weights else
        let append := (rec addLast xs := case! xs
          | inl(v) => inr((rejected, inl(#())))
          | inr(p) => inr(((fst(p)), addLast (snd(p)))));
        append weights);
      let encode := (rec convert xs := case! xs
        | inl(v) => inl(#())
        | inr(p) =>
          let m := (fst(p));
          let period := &Weighted.integerPower #2 (k - l);
          let encoded := (if m = denominator then ceiling - #1 else
            if l = k then m else if l = #0 then m else
            (m / (period - #1)) * period + m % (period - #1));
          inr((encoded, convert (snd(p)))));
      let rejectionIndex := (if rejected = #0 then #(-1) else &Occil.length weights);
      (encode values, (k, (l, rejectionIndex)))
    else fail

/-- Traverse a finite cyclic probability matrix directly, as nextFromMatrix.
The final column jumps back to l; rejection restarts the root state. -/
@[pl_fold] def optimalDraw : Exp rT := pl%
  fun table u,
    let matrix := (fst(table));
    let k := fst(snd(table));
    let l := fst(snd(snd(table)));
    let rejected := snd(snd(snd(table)));
    let scan := (rec search xs digit position index := case! xs
      | inl(v) => (#false, digit)
      | inr(p) =>
        let bit := ((fst(p)) / &Weighted.integerPower #2 position) % #2;
        let next := digit - bit;
        if next < #0 then (#true, index) else search (snd(p)) next position (index + #1));
    let walk := (rec draw value column :=
      let expanded := #2 * value + rand(#2, #());
      let outcome := scan matrix expanded (k - #1 - column) #0;
      if (fst(outcome)) then
        if (snd(outcome)) = rejected then draw #0 #0 else (snd(outcome))
      else draw (snd(outcome)) (if column + #1 = k then l else column + #1));
    walk #0 #0

@[pl_fold] def optimalChoice : Exp rT := pl%
  fun weights u,
    if &Weighted.validWeights weights then
      if &Occil.length weights = #1 then #0 else &optimalDraw (&optimalMatrix weights) #()
    else fail

end Occil.WeightedVariants
