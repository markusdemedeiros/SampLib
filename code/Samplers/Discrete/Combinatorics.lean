import Metrology.ProbLang.Syntax.Notation

/-!
# Integer combinatorics and count-vector operations

Object-language arithmetic and list operations shared by the discrete samplers.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Integer power, with a nonnegative exponent. -/
@[pl_fold] def integerPower : Exp rT := pl%
  fun base exponent,
    if exponent < #0 then fail else
      let loop := (rec go n product :=
        if n = #0 then product else go (n - #1) (product * base));
      loop exponent #1

/-- Binomial coefficient, with zero outside 0 <= k <= n. -/
@[pl_fold] def choose : Exp rT := pl%
  fun n k,
    if (n < #0) || (k < #0) || (n < k) then #0 else
      let loop := (rec go i product :=
        if k < i then product else
          go (i + #1) (product * (n - i + #1) / i));
      loop #1 #1

/-- Floor square root of a nonnegative integer, using Newton iteration. -/
@[pl_fold] def integerSqrt : Exp rT := pl%
  fun n,
    if n < #0 then fail else if n < #2 then n else
      let loop := (rec go x :=
        let next := (x + n / x) / #2;
        if x <= next then x else go next);
      loop n

/-- A list of n zero counters. -/
@[pl_fold] def zeroCounters : Exp rT := pl%
  rec build n := if n <= #0 then inl(#()) else inr((#0, build (n - #1)))

/-- Increment one element in an integer list. -/
@[pl_fold] def incrementCounter : Exp rT := pl%
  rec increment counters index := case! counters | inl(u) => fail | inr(p) =>
    if index = #0 then inr((fst(p) + #1, snd(p))) else
      inr((fst(p), increment (snd(p)) (index - #1)))

end Occil.DiscreteExtra
