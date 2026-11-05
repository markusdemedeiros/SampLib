import Samplers.Continuous

/-!
# Power factories and two-coin races.

Coin callbacks return fresh independent Booleans; rational parameters use integer pairs.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- p^(a/b), a>=0,b>0, combining integer and fractional powers. -/
@[pl_fold] def rationalPower : Exp rT := pl%
  fun coin a b u,
    if (a < #0) || (b <= #0) then fail else
      if &Occil.iterateCoin coin (a / b) then
        if a % b = #0 then #true else &Occil.fractionalPower coin (a % b) b #()
      else #false

/-- p^q with two unknown-probability input coins (Mendo's two-coin variant).
Requires q>0 when p=0; (p,q)=(0,0) does not terminate. -/
@[pl_fold] def twoCoinPower : Exp rT := pl%
  fun base exponent u,
    let loop := (rec draw i :=
      if base #() then #true else
      if exponent #() then
        if &Occil.rationalCoin #1 i then #false else draw (i + #1)
      else draw (i + #1));
    loop #1

/-- Portkey two-coin race. Weights x,y>=0; beta=a/b in (0,1].
Result beta*x*p / (beta*(x*p+y*q)+(1-beta)*(x+y)). -/
@[pl_fold] def twoCoin : Exp rT := pl%
  rec draw p q x y a b u :=
    if (x < #0) || (y < #0) || (x + y <= #0) then fail else
    if &Occil.rationalCoin a b then
      if &Occil.rationalCoin x (x + y) then
        if p #() then #true else draw p q x y a b #()
      else if q #() then #false else draw p q x y a b #()
    else #false

end Occil.FactoryExtra
