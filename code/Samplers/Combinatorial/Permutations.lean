import Samplers.Combinatorial.Basic
import Samplers.Continuous.Rejection

/-! Cycle permutations, derangements, and random bit flips. -/
namespace Occil

open ProbLang

variable {rT : Type _}

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
          if fst(p) = i then #false else check (snd(p)) (i + #1));
      &rejection (fun u, &shuffle (&intRange #0 n)) (fun xs, fixedPointFree xs #0) #()

/-- Randomly flip each bit independently according to an abstract coin. -/
@[pl_fold] def flipBits : Exp rT := pl%
  rec flip xs coin := case! xs | inl(u) => inl(#()) | inr(p) =>
    let bit := (if coin #() then ~(fst(p)) else (fst(p)));
    inr((bit, flip (snd(p)) coin))

end Occil
