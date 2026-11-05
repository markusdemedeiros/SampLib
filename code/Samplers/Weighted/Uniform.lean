import Samplers.Weighted.Core

/-! # Fair bits, uniform formats, and entropy recycling

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Bit generation, rejection, and recycling. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- Uniform integer made of exactly k independent fair bits. -/
@[pl_fold] def randomBits : Exp rT := pl%
  fun k,
    if k < #0 then fail else
      let loop := (rec read remaining value :=
        if remaining = #0 then value else
          read (remaining - #1) (value * #2 + rand(#2, #())));
      loop k #0

/-- Bitmask rejection: build a full ceil(log2(n))-bit candidate and retry. -/
@[pl_fold] def bitmaskRejection : Exp rT := pl%
  fun n,
    let limit := &powerOfTwoCeiling n;
    let candidate := (rec bits remaining value :=
      if remaining = #1 then value else
        bits (remaining / #2) (value * #2 + rand(#2, #())));
    let retry := (rec draw u :=
      let x := candidate limit #0;
      if x < n then x else draw #());
    retry #()

/-- FYKY's upper-interval acceptance form of uniform bit recycling. -/
@[pl_fold] def fyky : Exp rT := pl%
  fun n,
    if n <= #0 then fail else if n = #1 then #0 else
      let loop := (rec draw width value :=
        let w := width * #2;
        let v := value * #2 + rand(#2, #());
        if n <= w then
          if w - n <= v then v - (w - n) else draw (w - n) v
        else draw w v);
      loop #1 #0

/-- A reusable uniform entropy pool, storing (value,number of possible values). -/
@[pl_fold] def newRecycler : Exp rT := pl% fun u, alloc((#0, #1))

/-- Exact quotient/remainder recycling. Successful draws retain their unused
quotient in the pool; rejected high tails retain their conditional uniform law. -/
@[pl_fold] def recycledUniform : Exp rT := pl%
  fun pool n,
    if n <= #0 then fail else
      let initial := !pool;
      let loop := (rec draw value width :=
        if width < n then
          draw (value * #2 + rand(#2, #())) (width * #2)
        else
          let quotient := width / n;
          let accepted := quotient * n;
          if value < accepted then
            let result := value % n;
            pool ← ((value / n), quotient);
            result
          else draw (value - accepted) (width - accepted));
      loop (fst(initial)) (snd(initial))

/-- Repeated uniform draws using one persistent bit-recycling pool. -/
@[pl_fold] def recycledSamples : Exp rT := pl%
  fun n count,
    if count < #0 then fail else
      let pool := &newRecycler #();
      &Occil.repeatSample (fun u, &recycledUniform pool n) count

/-! ## Exact rational grids and explicit finite-format approximations. -/
/-- Exact rational grid sample in [0,1): result (numerator,denominator). -/
@[pl_fold] def uniformRational : Exp rT := pl%
  fun denominator u, (&Occil.uniformInt denominator, denominator)

/-- Exact dyadic grid sample: the denominator is 2^bits. -/
@[pl_fold] def uniformDyadic : Exp rT := pl%
  fun bits u,
    if bits < #0 then fail else (&randomBits bits, &integerPower #2 bits)

/-- Fixed-point output uses an explicit integer scale, not an opaque real type. -/
@[pl_fold] def uniformFixed : Exp rT := pl%
  fun scale u, &Occil.uniformInt scale

/-- Binary floating approximation to a uniform real: return (significand,exponent),
meaning significand*2^exponent. Leading zero digits determine the geometric
exponent. At maxZeros leading zeros, truncate to zero rather than loop forever.
This is a truncating finite-format sampler, not IEEE nearest rounding. -/
@[pl_fold] def uniformBinaryFloat : Exp rT := pl%
  fun precision maxZeros u,
    if (precision < #0) || (maxZeros < #0) then fail else
      let loop := (rec leading zeros :=
        if maxZeros <= zeros then (#0, #0) else
          if &Occil.fairCoin #() then
            (&integerPower #2 precision + &randomBits precision, -(zeros + precision + #1))
          else leading (zeros + #1));
      loop #0

end Occil.Weighted
