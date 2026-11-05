import Samplers.Lazy
import Samplers.Data

/-!
# Lazy values, uniform streams, comparisons and finite observations

A lazy number is an object-language function `bits ↦ (lo, (hi, denominator))`.
Every returned closed rational interval encloses the same latent value; requesting
more bits refines that value rather than sampling another one. Uniform streams
memoize their digits in the heap.

The operations use exact unbounded integers. Observations of genuinely continuous
values terminate almost surely; equal-value comparisons can remain undecided.
This interval-oracle representation follows the PSRN techniques in Occil's
`exporand.html`, rather than the site's packed-digit Python representation.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- Exact integer power for a nonnegative exponent. -/
@[pl_fold] def integerPower : Exp rT := pl%
  rec power x n :=
    if n < #0 then fail else if n = #0 then #1 else
      let half := power x (n / #2);
      if n % #2 = #0 then half * half else x * half * half

@[pl_fold] def rational : Exp rT := pl%
  fun numerator denominator,
    if denominator <= #0 then fail else
      fun bits, (numerator, (numerator, denominator))

@[pl_fold] def fromUniformBag : Exp rT := pl%
  fun bag, fun bits,
    if bits < #0 then fail else
      let numerator := &uniformBagPrefix bag bits;
      let denominator := &integerPower #2 bits;
      (numerator, (numerator + #1, denominator))

@[pl_fold] def newUniform : Exp rT := pl%
  fun u, let bag := &newUniformBag #(); &fromUniformBag bag

/-- Reveal the first n cached bits of a uniform bag; returns the original bag. -/
@[pl_fold] def fillUniformBag : Exp rT := pl%
  fun bag bits, let ignored := &uniformBagPrefix bag bits; bag

/-- Exact comparison of independent or shared oracle values whenever separated. -/
@[pl_fold] def less : Exp rT := pl%
  fun left right,
    let refine := (rec compare bits :=
      let a := left bits;
      let b := right bits;
      let ar := snd(a);
      let br := snd(b);
      if (fst(ar)) * (snd(br)) < (fst(b)) * (snd(ar)) then #true else
      if (fst(br)) * (snd(ar)) <= (fst(a)) * (snd(br)) then #false else
      compare (bits + #1));
    refine #1

/-- Refine until floor(scale*x) is unambiguous. The return is an integer, not
an IEEE float. Dyadic/grid boundary exceptions have the usual null-set caveat. -/
@[pl_fold] def floorScaled : Exp rT := pl%
  fun source scale,
    if scale <= #0 then fail else
      let refine := (rec observe bits :=
        let a := source bits;
        let range := snd(a);
        let lo := (fst(a)) * scale / (snd(range));
        let hi := (fst(range)) * scale / (snd(range));
        if lo = hi then lo else observe (bits + #1));
      refine #1

@[pl_fold] def rounded : Exp rT := pl%
  fun source bits,
    if bits < #0 then fail else &floorScaled source (&integerPower #2 bits)

/-- Compare two lazy uniforms directly, sharing their memoized digits. -/
@[pl_fold] def uniformLess : Exp rT := pl%
  rec compare left right :=
    let a := &uniformBagStep left;
    let b := &uniformBagStep right;
    if (fst(a)) = (fst(b)) then compare (snd(a)) (snd(b)) else
      if fst(a) then #false else #true

/-- FillGeometricBag in the binary prefix-stream representation. -/
@[pl_fold] def fillGeometricBag : Exp rT := pl%
  fun bag bits, &uniformBagPrefix bag bits

/-- General lazy proposal/acceptance engine; accepted state is preserved. -/
@[pl_fold] def newRejection : Exp rT := pl%
  rec draw proposal accept u :=
    let candidate := proposal #();
    if accept candidate then candidate else draw proposal accept #()

/-- Bernoulli(x) from a [0,1]-valued oracle, conditional on its cached latent
value. A fresh independent comparison uniform is created for every call. -/
@[pl_fold] def coin : Exp rT := pl%
  fun source u, &less (&newUniform #()) source

/-- Generic exact rejection inside a cube, for predicates on a list of lazy
coordinates. Input predicate must have positive acceptance probability. -/
@[pl_fold] def newInsideShape : Exp rT := pl%
  fun dimensions accept u,
    if dimensions <= #0 then fail else
      &newRejection (fun u, &repeatSample &newUniform dimensions) accept #()

end Occil.PSRN
