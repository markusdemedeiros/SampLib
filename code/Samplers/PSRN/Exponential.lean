import Samplers.PSRN.Uniform

/-!
# Exponential lazy samplers and conditional exponential trials

These constructions use exact coin transformations and cached digits.
Rates may be rational, logarithmic-rational, or supplied by an abstract coin.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- An e-rand from exact exp(-rate/d) coins. The integer part is geometric,
while digit k has probability 1/(1+exp(rate/2^k)), exactly as in Occil's
Sampling E-rands section. `decay divisor` is an independent Boolean trial. -/
@[pl_fold] def newExponentialFromDecay : Exp rT := pl%
  fun decay u,
    let count := (rec integerPart whole :=
      if decay #1 then integerPart (whole + #1) else whole);
    let whole := count #0;
    let digits := &newByDigits (fun seen denominator,
      let logistic := (rec trial u :=
        if &fairCoin #() then #false else
          if decay (denominator * #2) then #true else trial #());
      logistic #()) #();
    &add (&rational whole #1) digits

/-- Exponential PSRN at an arbitrary positive rational rate. -/
@[pl_fold] def newExponential : Exp rT := pl%
  fun numerator denominator u,
    if (numerator <= #0) || (denominator <= #0) then fail else
      &newExponentialFromDecay
        (fun divisor, &expMinusRational numerator (denominator * divisor) #()) #()

/-- Exponential PSRN with rate ln(x/y), x>y>0. -/
@[pl_fold] def newExponentialLogRate : Exp rT := pl%
  fun x y u,
    if (y <= #0) || (x <= y) then fail else
      &newExponentialFromDecay (fun divisor,
        &powerCoin (fun u, &rationalCoin y x) #1 divisor #()) #()

/-- Exponential PSRN with unknown positive rate p<=1 supplied as a p-coin. -/
@[pl_fold] def newExponentialUnknownRate : Exp rT := pl%
  fun coin u,
    &newExponentialFromDecay (fun divisor,
      &expMinusFactory (fun u,
        if coin #() then &rationalCoin #1 divisor else #false) #()) #()

/-- Conditional exp(-x) trial for a nonnegative lazy real x. -/
@[pl_fold] def expMinusCoin : Exp rT := pl%
  fun source u,
    let whole := &floorScaled source #1;
    if whole < #0 then fail else
      let fraction := &subtract source (&rational whole #1);
      if &expMinusRational whole #1 #() then
        &expMinusFactory (fun u, &coin fraction #()) #()
      else #false

end Occil.PSRN
