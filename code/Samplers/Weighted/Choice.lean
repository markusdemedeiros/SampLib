import Samplers.Weighted.Core
import Samplers.Discrete

/-! # Conditional, blocked, and expanded categorical tables

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Each method preserves its own preprocessing and draw algorithm. -/
namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Loaded die from sequential conditional coins. Integer weights need not be
normalized: the current remaining weight is the exact conditional denominator. -/
@[pl_fold] def sequentialCoins : Exp rT := pl%
  fun weights u,
    if &Weighted.validWeights weights then
      let loop := (rec choose xs remaining index := case! xs
        | inl(v) => fail
        | inr(p) =>
          if &Occil.rationalCoin (fst(p)) remaining then index else
            choose (snd(p)) (remaining - (fst(p))) (index + #1));
      loop weights (&Occil.sumInts weights) #0
    else fail

/-- A two-level categorical search: choose a block by its total weight, then
choose within that block by conditional weights. Integer block size is explicit. -/
@[pl_fold] def twoLevelChoice : Exp rT := pl%
  fun weights blockSize u,
    if blockSize <= #0 then fail else
    if &Weighted.validWeights weights then
      let chunks := (rec group xs := case! xs
        | inl(v) => inl(#())
        | inr(p) =>
          let split := (rec take ys remaining :=
            if remaining = #0 then (inl(#()), ys) else case! ys
              | inl(v) => (inl(#()), inl(#()))
              | inr(q) =>
                let rest := take (snd(q)) (remaining - #1);
                (inr(((fst(q)), (fst(rest)))), (snd(rest))));
          let part := split xs blockSize;
          inr(((fst(part)), group (snd(part)))));
      let blocks := chunks weights;
      let totals := (rec sumBlocks xs := case! xs
        | inl(v) => inl(#())
        | inr(p) => inr((&Occil.sumInts (fst(p)), sumBlocks (snd(p)))));
      let selected := &Occil.weightedChoice (totals blocks);
      selected * blockSize + &Occil.weightedChoice (&Occil.getAt blocks selected)
    else fail

/-- Flat sampling table: each unit of integer weight stores one category entry.
Memory is proportional to the total weight; draws require one indexed lookup. -/
@[pl_fold] def flatChoice : Exp rT := pl%
  fun weights u,
    if &Weighted.validWeights weights then
      let build := (rec expand xs index := case! xs
        | inl(v) => inl(#())
        | inr(p) =>
          let copies := (rec copiesOf remaining := if remaining = #0 then expand (snd(p)) (index + #1)
            else inr((index, copiesOf (remaining - #1))));
          copies (fst(p)));
      let table := build weights #0;
      &Occil.getAt table (&Occil.uniformInt (&Occil.sumInts weights))
    else fail

end Occil.WeightedVariants
