import Samplers.Weighted.Trees

/-! # Structured categorical rejection envelopes

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Sorted dyadic envelopes and packed integer weights. -/
namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Bringmann–Panagiotou's sorted-weight dyadic envelope groups, using FLDR
for the envelope-group draw. Weights must be monotone, ascending or descending. -/
@[pl_fold] def sortedChoice : Exp rT := pl%
  fun weights u,
    let n := &Occil.length weights;
    if &Weighted.validWeights weights then
      if n = #1 then #0 else
        let ascending := (&Occil.getAt weights #0 <= &Occil.getAt weights (n - #1));
        let check := (rec monotone xs := case! xs
          | inl(v) => #true
          | inr(p) => case! (snd(p))
            | inl(v) => #true
            | inr(q) =>
              if ascending then
                if (fst(q)) < (fst(p)) then #false else monotone (snd(p))
              else if (fst(p)) < (fst(q)) then #false else monotone (snd(p)));
        if check weights then
          let groups := (rec build lower := if n < lower then inl(#()) else
            let upper := (if n < #2 * lower - #1 then n else #2 * lower - #1);
            let pivot := (if ascending then n - lower else lower - #1);
            let envelope := &Occil.getAt weights pivot;
            inr(((upper - lower + #1) * envelope, build (#2 * lower))));
          let envelopes := groups #1;
          let loop := (rec draw v :=
            let k := &Weighted.fastLoadedDiceRoller envelopes #();
            let lower := &Weighted.integerPower #2 k;
            let upper := (if n < #2 * lower - #1 then n else #2 * lower - #1);
            let offset := &Occil.rndIntRange lower upper - #1;
            let index := (if ascending then n - #1 - offset else offset);
            let pivot := (if ascending then n - lower else lower - #1);
            if &Occil.rationalCoin (&Occil.getAt weights index) (&Occil.getAt weights pivot)
              then index else draw #());
          loop #()
        else fail
    else fail

/-- Bringmann–Larsen's packed 20/32-bit weights. Uses the source's max-weight
rejection optimization. Weights >=2^32 are rejected in the packed branch. -/
@[pl_fold] def succinctChoice : Exp rT := pl%
  fun weights u,
    if &Weighted.validWeights weights then
      let n := &Occil.length weights;
      let maximum := (rec largest xs current := case! xs
        | inl(v) => current
        | inr(p) => largest (snd(p)) (if current < (fst(p)) then (fst(p)) else current));
      let bound := maximum weights #0;
      if &Weighted.integerPower #2 #19 * n <= &Occil.sumInts weights then
        let loop := (rec draw v :=
          let i := &Occil.uniformInt n;
          if &Occil.rationalCoin (&Occil.getAt weights i) bound then i else draw #());
        loop #()
      else
        let pack := (rec encode xs index offset bits shorts := case! xs
          | inl(v) => (bits, shorts)
          | inr(p) =>
            let weight := (fst(p));
            if &Weighted.integerPower #2 #32 <= weight then fail else
              let wide := (&Weighted.integerPower #2 #20 <= weight);
              let width := (if wide then #32 else #20);
              let mask := (if wide then shorts + &Weighted.integerPower #2 index else shorts);
              encode (snd(p)) (index + #1) (offset + width)
                (bits + weight * &Weighted.integerPower #2 offset) mask);
        let packed := pack weights #0 #0 #0 #0;
        let bits := (fst(packed));
        let shorts := (snd(packed));
        let rank := (rec count i value := if i = #0 then #0 else
          value % #2 + count (i - #1) (value / #2));
        let loop := (rec draw v :=
          let i := &Occil.uniformInt n;
          let wideBefore := rank i shorts;
          let offset := #32 * wideBefore + #20 * (i - wideBefore);
          let width := (if (shorts / &Weighted.integerPower #2 i) % #2 = #1 then #32 else #20);
          let weight := (bits / &Weighted.integerPower #2 offset) %
            &Weighted.integerPower #2 width;
          if &Occil.rationalCoin weight bound then i else draw #());
        loop #()
    else fail

end Occil.WeightedVariants
