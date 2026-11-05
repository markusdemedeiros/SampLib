import Samplers.Weighted.Core

/-! # Probability-matrix categorical samplers

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Knuth–Yao, FLDR, and Han–Hoshi are distinct entropy-oriented algorithms. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- Scan a binary probability column. Returns inl(label) on reaching a leaf,
otherwise inr(distance) after subtracting all leaves in the column. -/
@[pl_fold] def matrixColumn : Exp rT := pl%
  rec scan weights multiplier denominator distance label :=
    case! weights
      | inl(u) => inr(distance)
      | inr(p) =>
          let bit := ((fst(p)) * multiplier / denominator) % #2;
          if distance < bit then inl(label)
          else scan (snd(p)) multiplier denominator (distance - bit) (label + #1)

/-- Knuth–Yao walk over the binary expansions of the exact rational probabilities.
The matrix is generated column by column, rather than eagerly storing a DDG tree. -/
@[pl_fold] def knuthYao : Exp rT := pl%
  fun weights u,
    if &validWeights weights then
      let total := &Occil.sumInts weights;
      let singleton := (rec find xs i := case! xs
        | inl(u) => #(-1)
        | inr(p) => if (fst(p)) = total then i else find (snd(p)) (i + #1));
      let certain := singleton weights #0;
      if #0 <= certain then certain else
        let loop := (rec draw multiplier distance :=
          let next := distance * #2 + rand(#2, #());
          case! (&matrixColumn weights multiplier total next #0)
            | inl(label) => label
            | inr(rest) => draw (multiplier * #2) rest);
        loop #2 #0
    else fail

/-- Fast Loaded Dice Roller with the dyadic rejection outcome appended implicitly.
The finite probability matrix is traversed directly; the padded outcome restarts. -/
@[pl_fold] def fastLoadedDiceRoller : Exp rT := pl%
  fun weights u,
    if &validWeights weights then
      let total := &Occil.sumInts weights;
      let padded := &powerOfTwoCeiling total;
      let singleton := (rec find xs i := case! xs
        | inl(u) => #(-1)
        | inr(p) => if (fst(p)) = total then i else find (snd(p)) (i + #1));
      let certain := singleton weights #0;
      if #0 <= certain then certain else
        let loop := (rec draw place distance :=
          let next := distance * #2 + rand(#2, #());
          let scan := (rec column xs d label := case! xs
            | inl(v) =>
                let rejectionBit := ((padded - total) / place) % #2;
                if d < rejectionBit then draw (padded / #2) #0
                else draw (place / #2) (d - rejectionBit)
            | inr(p) =>
                let bit := ((fst(p)) / place) % #2;
                if d < bit then label else column (snd(p)) (d - bit) (label + #1));
          if place <= #0 then fail else scan weights next #0);
        loop (padded / #2) #0
    else fail

/-- Han–Hoshi interval refinement: a fair-bit cell is refined until it lies
entirely inside one cumulative-probability interval. Exact integer comparisons. -/
@[pl_fold] def hanHoshi : Exp rT := pl%
  fun weights u,
    if &validWeights weights then
      let total := &Occil.sumInts weights;
      let find := (rec visit xs previous value denominator label := case! xs
        | inl(v) => #(-1)
        | inr(p) =>
            let next := previous + fst(p);
            if (previous * denominator <= value * total) &&
               ((value + #1) * total <= next * denominator) then label
            else visit (snd(p)) next value denominator (label + #1));
      let loop := (rec refine value denominator :=
        let label := find weights #0 value denominator #0;
        if #0 <= label then label else
          refine (value * #2 + rand(#2, #())) (denominator * #2));
      loop #0 #1
    else fail

end Occil.Weighted
