import Samplers.Weighted.Core

/-! # Heap-backed Vose alias tables

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Small/large-stack preprocessing and repeated draws. -/
namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Vose alias preprocessing with explicit small/large stacks. Returned table:
(n,(total,(thresholdArray,aliasArray))). Arrays are retained in the heap. -/
@[pl_fold] def voseTable : Exp rT := pl%
  fun weights,
    if &Weighted.validWeights weights then
      let n := &Occil.length weights;
      let total := &Occil.sumInts weights;
      let work := allocN(n, #0);
      let probability := allocN(n, total);
      let aliases := allocN(n, #0);
      let small := alloc(inl(#()));
      let large := alloc(inl(#()));
      let setup := (rec fill xs index := case! xs
        | inl(v) => #()
        | inr(p) =>
          let mass := n * (fst(p));
          (work +ₗ index) ← mass;
          (aliases +ₗ index) ← index;
          (if mass < total then small ← inr((index, !small))
            else large ← inr((index, !large)));
          fill (snd(p)) (index + #1));
      setup weights #0;
      let balance := (rec prepare u := case! !small
        | inl(v) => #()
        | inr(s) => case! !large
          | inl(v) => #()
          | inr(g) =>
            let lo := (fst(s));
            let hi := (fst(g));
            let mass := !(work +ₗ lo);
            let remainder := !(work +ₗ hi) + mass - total;
            (probability +ₗ lo) ← mass;
            (aliases +ₗ lo) ← hi;
            (work +ₗ hi) ← remainder;
            (if remainder < total then
              (small ← inr((hi, (snd(s)))); large ← (snd(g)))
            else small ← (snd(s)));
            prepare #());
      balance #();
      (n, (total, (probability, aliases)))
    else fail

@[pl_fold] def voseDraw : Exp rT := pl%
  fun table u,
    let n := (fst(table));
    let total := fst(snd(table));
    let probability := fst(snd(snd(table)));
    let aliases := snd(snd(snd(table)));
    let i := &Occil.uniformInt n;
    let alternative := !(aliases +ₗ i);
    if i = alternative then i else
      if &Occil.uniformInt total < !(probability +ₗ i) then i else alternative

@[pl_fold] def voseSamples : Exp rT := pl%
  fun weights count,
    if count < #0 then fail else
      let table := &voseTable weights;
      &Occil.repeatSample (fun u, &voseDraw table #()) count

end Occil.WeightedVariants
