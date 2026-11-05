import Samplers.Data

/-! # Integer weights and arithmetic

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Weights must be nonnegative with positive total; integer arithmetic is exact. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- Nonnegative integer weights with a strictly positive sum. -/
@[pl_fold] def validWeights : Exp rT := pl%
  fun weights,
    let check := (rec visit xs := case! xs
      | inl(u) => #true
      | inr(p) => if (fst(p)) < #0 then #false else visit (snd(p)));
    if check weights then #0 < &Occil.sumInts weights else #false

/-- Integer powers, including x^0=1; negative exponents are rejected. -/
@[pl_fold] def integerPower : Exp rT := pl%
  rec power x n :=
    if n < #0 then fail else
    if n = #0 then #1 else
      let half := power x (n / #2);
      if n % #2 = #0 then half * half else x * half * half

/-- Smallest power of two at least n, for n>0. -/
@[pl_fold] def powerOfTwoCeiling : Exp rT := pl%
  fun n,
    if n <= #0 then fail else
      let loop := (rec double value :=
        if n <= value then value else double (value * #2));
      loop #1

/-! ## Bit-length helper for the bounded-word algorithms. -/

end Occil.Weighted

namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Positive integer bit length; bitLength(0)=0. -/
@[pl_fold] def bitLength : Exp rT := pl%
  rec count n := if n < #0 then fail else if n = #0 then #0 else #1 + count (n / #2)

end Occil.WeightedVariants
