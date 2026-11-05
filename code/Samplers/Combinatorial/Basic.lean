import Samplers.Discrete

/-! Sampling collections from randomfunc.html. Heap arrays are temporary;
all returned collections use the list encoding in Samplers.Data. -/
namespace Occil

open ProbLang

variable {rT : Type _}

@[pl_fold] def choice : Exp rT := pl%
  fun xs, &getAt xs (&uniformInt (&length xs))

@[pl_fold] def sampleWithReplacement : Exp rT := pl%
  fun xs k, if k < #0 then fail else &repeatSample (fun u, &choice xs) k

@[pl_fold] def sampleWithoutReplacement : Exp rT := pl%
  rec draw xs k :=
    if (k < #0) || (&length xs < k) then fail else
    if k = #0 then inl(#()) else
      let p := &removeAt xs (&uniformInt (&length xs));
      inr((fst(p), draw (snd(p)) (k - #1)))

/-- Select k items in input order; fixes the article's `u <= kk` to `u < kk`. -/
@[pl_fold] def sampleInOrder : Exp rT := pl%
  fun xs k,
    let n := &length xs;
    if (k < #0) || (n < k) then fail else
      let draw := (rec go ys remaining needed :=
        if needed = #0 then inl(#()) else
        case! ys | inl(u) => fail | inr(p) =>
          if &uniformInt remaining < needed then
            inr((fst(p), go (snd(p)) (remaining - #1) (needed - #1)))
          else go (snd(p)) (remaining - #1) needed);
      draw xs n k

@[pl_fold] def fillArray : Exp rT := pl%
  rec fill a xs i := case! xs | inl(u) => #() | inr(p) =>
    ((a +ₗ i) ← (fst(p)); fill a (snd(p)) (i + #1))

@[pl_fold] def readArray : Exp rT := pl%
  rec read a i n := if i = n then inl(#()) else
    let x := !(a +ₗ i);
    inr((x, read a (i + #1) n))

/-- Durstenfeld/Fisher-Yates. Uses j consistently (the source prints k in swaps). -/
@[pl_fold] def shuffle : Exp rT := pl%
  fun xs,
    let n := &length xs;
    if n = #0 then inl(#()) else
      let a := allocN(n, #());
      &fillArray a xs #0;
      let swap := (rec go i := if i <= #0 then #() else
        let j := &uniformInt (i + #1);
        let x := !(a +ₗ i);
        let y := !(a +ₗ j);
        (a +ₗ i) ← y;
        (a +ₗ j) ← x;
        go (i - #1));
      swap (n - #1);
      &readArray a #0 n

/-- Reservoir Algorithm R over a finite list. Returns the reservoir slots;
its unordered k-subset is uniform. No final shuffle is promised. -/
@[pl_fold] def reservoir : Exp rT := pl%
  fun xs k,
    let n := &length xs;
    if (k < #0) || (n < k) then fail else if k = #0 then inl(#()) else
      let a := allocN(k, #());
      let scan := (rec go ys i := case! ys | inl(u) => #() | inr(p) =>
        if i < k then
          ((a +ₗ i) ← (fst(p)); go (snd(p)) (i + #1))
        else
          let j := &uniformInt (i + #1);
          if j < k then
            ((a +ₗ j) ← (fst(p)); go (snd(p)) (i + #1))
          else go (snd(p)) (i + #1));
      scan xs #0;
      &readArray a #0 k

/-- The increasing integer list [lo,hi). -/
@[pl_fold] def intRange : Exp rT := pl%
  rec range lo hi := if hi <= lo then inl(#()) else inr((lo, range (lo + #1) hi))

/-- Uniform positive composition by uniformly chosen ordered cut points. -/
@[pl_fold] def positiveComposition : Exp rT := pl%
  fun n total,
    if (n <= #0) || (total < n) then fail else
      let cuts := &sampleInOrder (&intRange #1 total) (n - #1);
      let differences := (rec go prev xs := case! xs
        | inl(u) => inr((total - prev, inl(#())))
        | inr(p) => inr((fst(p) - prev, go (fst(p)) (snd(p)))));
      differences #0 cuts

@[pl_fold] def weakComposition : Exp rT := pl%
  fun n total,
    if total < #0 then fail else
      let parts := &positiveComposition n (total + n);
      let subtract := (rec go xs := case! xs | inl(u) => inl(#())
        | inr(p) => inr((fst(p) - #1, go (snd(p)))));
      subtract parts

/-- G(n,p) by independent edge indicators; output is a list of (i,j), i<j.
This is the direct construction, not the article's geometric skip optimization. -/
@[pl_fold] def randomGraph : Exp rT := pl%
  fun n coin,
    if n < #0 then fail else
      let rows := (rec outer i := if n <= i then inl(#()) else
        let columns := (rec inner j := if n <= j then outer (i + #1) else
          if coin #() then inr(((i, j), inner (j + #1))) else inner (j + #1));
        columns (i + #1));
      rows #0

end Occil
