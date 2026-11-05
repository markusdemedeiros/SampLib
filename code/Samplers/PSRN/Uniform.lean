import Samplers.PSRN.Arithmetic
import Samplers.Continuous

/-!
# Uniform order statistics, transforms and conditional digit streams

Uniform transformations retain their underlying cached random values.
Conditional digit callbacks specify their own law; unsampled tails are not
automatically filled with independent fair bits.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- Select k-th of n independent lazy uniforms without filling unsampled tails. -/
@[pl_fold] def newOrderStatistic : Exp rT := pl%
  fun n k,
    if (n <= #0) || (k <= #0) || (n < k) then fail else
      let insert := (rec put x xs := case! xs
        | inl(u) => inr((x, inl(#())))
        | inr(p) => if &less x (fst(p)) then inr((x, xs)) else
          inr((fst(p), put x (snd(p)))));
      let build := (rec draw remaining := if remaining = #0 then inl(#()) else
        let x := &newUniform #();
        insert x (draw (remaining - #1)));
      &getAt (build n) (k - #1)

/-- Uniform raised to a rational power; negative powers have unbounded tails. -/
@[pl_fold] def newPowerUniform : Exp rT := pl%
  fun numerator denominator u,
    if denominator <= #0 then fail else
      let x := &newUniform #();
      &powerRational x numerator denominator

/-- Raise an abstract coin's probability to a nonnegative rational power. -/
@[pl_fold] def powerCoin : Exp rT := pl%
  fun coin numerator denominator u,
    if (numerator < #0) || (denominator <= #0) then fail else
      let whole := &iterateCoin coin (numerator / denominator);
      if whole then
        let rest := numerator % denominator;
        if rest = #0 then #true else &fractionalPower coin rest denominator #()
      else #false

/-- A generic memoized digit sampler. `nextBit prefix denominator` must sample
the next conditional digit given the already cached prefix. Returns an oracle.
This interface can represent dependent/nonuniform digits; it never fills them
with fair bits unless `nextBit` itself specifies a uniform conditional law. -/
@[pl_fold] def newByDigits : Exp rT := pl%
  fun nextBit u,
    let first := &newUniformBag #();
    fun bits,
      if bits < #0 then fail else
        let read := (rec readDigits node remaining numerator denominator :=
          if remaining = #0 then (numerator, (numerator + #1, denominator)) else
            let p := !node;
            let step := (case! p
              | inl(v) =>
                let tail := &newUniformBag #();
                let bit := nextBit numerator denominator;
                let value := (bit, tail);
                node ← inr(value);
                value
              | inr(value) => value);
            let digit := (if fst(step) then #1 else #0);
            readDigits (snd(step)) (remaining - #1) (numerator * #2 + digit) (denominator * #2));
        read first bits #0 #1

@[pl_fold] def newUniformSum : Exp rT := pl%
  rec draw n := if n < #0 then fail else if n = #0 then &rational #0 #1 else
    let x := &newUniform #();
    &add x (draw (n - #1))

@[pl_fold] def newRatioUniforms : Exp rT := pl%
  fun u, let a := &newUniform #(); let b := &newUniform #(); &divide a b

@[pl_fold] def newReciprocalUniform : Exp rT := pl%
  fun u, &reciprocal (&newUniform #())

@[pl_fold] def newReciprocalPowerUniform : Exp rT := pl%
  fun numerator denominator u,
    &reciprocal (&newPowerUniform numerator denominator #())

@[pl_fold] def newOddsUniform : Exp rT := pl%
  fun u,
    let x := &newUniform #();
    &divide x (&subtract (&rational #1 #1) x)

end Occil.PSRN
