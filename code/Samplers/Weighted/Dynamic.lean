import Samplers.Weighted.Core
import Samplers.Combinatorial

/-! # Mutable cumulative weights

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Fenwick-tree construction, replacement, and inversion. -/
namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- The least significant set-bit value of a positive integer. -/
@[pl_fold] def lowBit : Exp rT := pl%
  fun value,
    if value <= #0 then fail else
      let loop := (rec count rest result :=
        if rest % #2 = #1 then result else count (rest / #2) (#2 * result));
      loop value #1

/-- Mutable cumulative weights in a Fenwick tree. Returns
`(n,(totalReference,(weightArray,treeArray)))`. This supports the changing-weight
use case in the comparison table; it is not a claim to reproduce every data
structure or performance result in the Klundert survey. -/
@[pl_fold] def newFenwick : Exp rT := pl%
  fun weights,
    if &Weighted.validWeights weights then
      let n := &Occil.length weights;
      let total := alloc(&Occil.sumInts weights);
      let values := allocN(n, #0);
      let tree := allocN(n + #1, #0);
      &Occil.fillArray values weights #0;
      let add := (rec propagate i amount :=
        if n < i then #() else
          let previous := !(tree +ₗ i);
          (tree +ₗ i) ← (previous + amount);
          propagate (i + &lowBit i) amount);
      let initializeTree := (rec build xs i := case! xs
        | inl(v) => #()
        | inr(p) => (add i (fst(p)); build (snd(p)) (i + #1)));
      initializeTree weights #1;
      (n, (total, (values, tree)))
    else fail

/-- Replace one weight and update every affected cumulative-tree node. -/
@[pl_fold] def fenwickSet : Exp rT := pl%
  fun table index weight,
    let n := (fst(table));
    let total := fst(snd(table));
    let values := fst(snd(snd(table)));
    let tree := snd(snd(snd(table)));
    if (index < #0) || (n <= index) || (weight < #0) then fail else
      let difference := weight - !(values +ₗ index);
      let previousTotal := !total;
      total ← (previousTotal + difference);
      (values +ₗ index) ← weight;
      let add := (rec propagate i :=
        if n < i then #() else
          let previous := !(tree +ₗ i);
          (tree +ₗ i) ← (previous + difference);
          propagate (i + &lowBit i));
      add (index + #1)

/-- Invert cumulative mass by binary lifting through a mutable Fenwick tree. -/
@[pl_fold] def fenwickDraw : Exp rT := pl%
  fun table u,
    let n := (fst(table));
    let total := fst(snd(table));
    let tree := snd(snd(snd(table)));
    let target := &Occil.uniformInt (!total);
    let loop := (rec search step index remaining :=
      if step = #0 then index else
        let next := index + step;
        if n < next then search (step / #2) index remaining else
          let mass := !(tree +ₗ next);
          if mass <= remaining then search (step / #2) next (remaining - mass)
          else search (step / #2) index remaining);
    loop (&Weighted.powerOfTwoCeiling n) #0 target

end Occil.WeightedVariants
