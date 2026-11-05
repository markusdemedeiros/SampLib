import Samplers.Uniform

/-! Bernoulli factories, from bernoulli.html and bernoulli.py.
Input coins are unit-taking object-language functions, never inspected probabilities. -/
namespace Occil
open ProbLang
variable {rT : Type _}

@[pl_fold] def complement : Exp rT := pl% fun coin u, ~(coin #())

@[pl_fold] def coinProduct : Exp rT := pl%
  fun p q u, if p #() then q #() else #false

@[pl_fold] def coinDisjunction : Exp rT := pl%
  fun p q u, if p #() then #true else q #()

@[pl_fold] def coinMean : Exp rT := pl%
  fun p q u, if &fairCoin #() then p #() else q #()

@[pl_fold] def coinConditional : Exp rT := pl%
  fun p q select u, if select #() then p #() else q #()

/-- von Neumann extraction; requires 0<p<1. -/
@[pl_fold] def vonNeumann : Exp rT := pl%
  rec draw coin u :=
    let a := coin #();
    let b := coin #();
    if a = b then draw coin #() else a

/-- p/(p+q) via a two-coin Bernoulli race, requiring p+q>0. -/
@[pl_fold] def bernoulliRace : Exp rT := pl%
  rec race p q u := if &fairCoin #() then
    if p #() then #true else race p q #()
  else if q #() then #false else race p q #()

/-- 1/(1+p); expected number of iterations <=2, including p=1. -/
@[pl_fold] def oneDivOnePlus : Exp rT := pl%
  rec draw coin u := if &fairCoin #() then #true else
    if coin #() then #false else draw coin #()

/-- 1/(1+p) by parity of successes before failure; requires p<1. -/
@[pl_fold] def evenParity : Exp rT := pl%
  rec draw coin u := if coin #() then
    if coin #() then draw coin #() else #false
  else #true

/-- p^(a/b), 0<a<=b, by Mendo's factory. At p=0 it terminates a.s.
but can have infinite expected cost; tests avoid that heavy-tail endpoint. -/
@[pl_fold] def fractionalPower : Exp rT := pl%
  fun coin a b u,
    if (a <= #0) || (b < a) then fail else
      let loop := (rec go i := if coin #() then #true else
        if &rationalCoin a (b * i) then #false else go (i + #1));
      loop #1

/-- exp(-x/y), x>=0,y>0; alternating-series parity with rational coins.
Integer part factors into independent exp(-1) trials. -/
@[pl_fold] def expMinusRational : Exp rT := pl%
  fun x y u,
    if (x < #0) || (y <= #0) then fail else
      let small := (fun numerator denominator,
        let loop := (rec go i parity :=
          if &rationalCoin numerator (denominator * i) then go (i + #1) (~parity)
          else parity);
        loop #1 #true);
      let whole := (rec rep n := if n = #0 then #true else
        if small #1 #1 then rep (n - #1) else #false);
      if whole (x / y) then small (x % y) y else #false

/-- exp(-p) from an abstract p-coin: a decreasing-uniform alternating trial.
Survival through n iterations has probability p^n/n!. -/
@[pl_fold] def expMinusFactory : Exp rT := pl%
  fun coin u,
    let loop := (rec go previous parity :=
      let x := urand;
      if x < previous then
        if coin #() then go x (~parity) else parity
      else parity);
    loop (toReal(#1)) #true

end Occil
