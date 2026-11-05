import Metrology.ProbLang.Syntax.Notation

/-! Uniform integers and coins. Source: randomfunc.html, Uniform Random Integers
and Boolean Conditions. Arguments are integers unless explicitly stated otherwise. -/
namespace Occil
open ProbLang
variable {rT : Type _}

/-- Uniform integer in [0,n). Requires n > 0. -/
@[pl_fold] def uniformInt : Exp rT := pl%
  fun n, if #0 < n then rand(n, #()) else fail

/-- RNDINT: inclusive upper bound, including the deterministic zero case. -/
@[pl_fold] def rndInt : Exp rT := pl%
  fun hi, if hi < #0 then fail else if hi = #0 then #0 else &uniformInt (hi + #1)

@[pl_fold] def rndIntRange : Exp rT := pl%
  fun lo hi, if hi < lo then fail else lo + &rndInt (hi - lo)

@[pl_fold] def rndIntExcRange : Exp rT := pl%
  fun lo hi, if lo < hi then lo + &uniformInt (hi - lo) else fail

/-- Lumbroso Fast Dice Roller, one fair bit per iteration; exclusive bound n. -/
@[pl_fold] def fastDiceRoller : Exp rT := pl%
  fun n,
    if n <= #0 then fail else if n = #1 then #0 else
    let loop := (rec go v c :=
      let vv := v * #2;
      let cc := c * #2 + rand(#2, #());
      if n <= vv then
        if cc < n then cc else go (vv - n) (cc - n)
      else go vv cc);
    loop #1 #0

/-- Occil's non-power-of-two helper, including recursive expansion when the
requested range exceeds the source modulus. Result in [0,n), modulus >= 2. -/
@[pl_fold] def uniformFromModulus : Exp rT := pl%
  rec draw modulus n :=
    if (modulus < #2) || (n <= #0) then fail else
    if n <= modulus then
      let limit := ((modulus - #1) / n) * n;
      let retry := (rec go u :=
        let x := rand(modulus, #());
        if x < n then x else if x < limit then x % n else go #());
      retry #()
    else
      let width := (n - #1) / modulus + #1;
      let retry := (rec go u :=
        let high := rand(modulus, #());
        let low := draw modulus width;
        let x := width * high + low;
        if x < n then x else go #());
      retry #()

@[pl_fold] def fairCoin : Exp rT := pl% fun u, rand(#2, #()) = #1

/-- Exact rational coin; fail for invalid parameters rather than silently clamp. -/
@[pl_fold] def rationalCoin : Exp rT := pl%
  fun numerator denominator,
    if (denominator <= #0) || (numerator < #0) || (denominator < numerator) then fail else
    if numerator = #0 then #false else if numerator = denominator then #true else
    rand(denominator, #()) < numerator

/-- Ideal continuous threshold coin, with a checked unit-interval domain. -/
@[pl_fold] def realCoin : Exp rT := pl%
  fun p, if (p < toReal(#0)) || (toReal(#1) < p) then fail else urand < p

end Occil
