import Samplers.Uniform

/-!
# Integer and rational arithmetic for callback-coin factories.

These are object-language support terms. Rational values use canonical integer pairs.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- Integer binomial coefficient, with zero outside 0 <= k <= n. -/
@[pl_fold] def choose : Exp rT := pl%
  fun n k,
    if (n < #0) || (k < #0) || (n < k) then #0 else
      let loop := (rec product i value :=
        if k < i then value else product (i + #1) (value * (n - k + i) / i));
      loop #1 #1

@[pl_fold] def intPower : Exp rT := pl%
  rec power x n := if n < #0 then fail else
    if n = #0 then #1 else x * power x (n - #1)

/-- Canonical rational pair, used to keep adaptive envelope arithmetic small. -/
@[pl_fold] def fraction : Exp rT := pl%
  fun numerator denominator,
    if denominator = #0 then fail else
      let sign := (if denominator < #0 then #(-1) else #1);
      let n := numerator * sign;
      let d := denominator * sign;
      let absolute := (if n < #0 then -n else n);
      let gcd := (rec reduce a b := if b = #0 then a else reduce b (a % b));
      let divisor := gcd absolute d;
      (n / divisor, d / divisor)

@[pl_fold] def addFraction : Exp rT := pl%
  fun a b,
    &fraction ((fst(a)) * (snd(b)) + (fst(b)) * (snd(a))) ((snd(a)) * (snd(b)))

@[pl_fold] def subtractFraction : Exp rT := pl%
  fun a b,
    &fraction ((fst(a)) * (snd(b)) - (fst(b)) * (snd(a))) ((snd(a)) * (snd(b)))

@[pl_fold] def multiplyFraction : Exp rT := pl%
  fun a b, &fraction ((fst(a)) * (fst(b))) ((snd(a)) * (snd(b)))

@[pl_fold] def divideFraction : Exp rT := pl%
  fun a b, &fraction ((fst(a)) * (snd(b))) ((snd(a)) * (fst(b)))

end Occil.FactoryExtra
