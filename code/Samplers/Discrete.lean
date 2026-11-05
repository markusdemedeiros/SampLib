import Samplers.Data

/-! Discrete samplers from randomfunc.html: dice, Bernoulli trials, weighted
choice, multinomial and Pólya–Eggenberger urn sampling. -/
namespace Occil
open ProbLang
variable {rT : Type _}

/-- Direct independent-trial binomial construction; callback returns a Boolean. -/
@[pl_fold] def binomial : Exp rT := pl%
  rec draw coin n := if n < #0 then fail else if n = #0 then #0 else
    let b := coin #();
    let rest := draw coin (n - #1);
    if b then rest + #1 else rest

/-- Failures before first success. Requires an almost-surely terminating coin
with positive success probability; p=0 deliberately diverges. -/
@[pl_fold] def geometric : Exp rT := pl%
  rec draw coin u := if coin #() then #0 else #1 + draw coin #()

@[pl_fold] def negativeBinomial : Exp rT := pl%
  rec draw coin successes := if successes < #0 then fail else
    if successes = #0 then #0 else
      &geometric coin #() + draw coin (successes - #1)

@[pl_fold] def dice : Exp rT := pl%
  rec roll count sides := if (count < #0) || (sides <= #0) then fail else
    if count = #0 then #0 else #1 + &uniformInt sides + roll (count - #1) sides

/-- Cumulative weighted choice: nonnegative integer weights, positive total. -/
@[pl_fold] def weightedChoice : Exp rT := pl%
  fun weights,
    let check := (rec valid xs := case! xs | inl(u) => #true
      | inr(p) => if (fst(p)) < #0 then #false else valid (snd(p)));
    if check weights then
      let total := &sumInts weights;
      let x := &uniformInt total;
      let select := (rec go xs value i := case! xs | inl(u) => fail
        | inr(p) => if value < (fst(p)) then i else go (snd(p)) (value - (fst(p))) (i + #1));
      select weights x #0
    else fail

/-- Sequential conditional binomials; return one count per category.
Corrects the article's inconsistent `t` variable and expresses renormalization
by integer remaining-weight sums. -/
@[pl_fold] def multinomial : Exp rT := pl%
  rec draw n weights :=
    if n < #0 then fail else
    case! weights
      | inl(u) => if n = #0 then inl(#()) else fail
      | inr(p) =>
        if (fst(p)) < #0 then fail else
        let total := &sumInts weights;
        if total <= #0 then if n = #0 then
          inr((#0, draw #0 (snd(p)))) else fail
        else
          let k := &binomial (fun u, &rationalCoin (fst(p)) total) n;
          inr((k, draw (n - k) (snd(p))))

/-- Reinforced urn, integer reinforcement >= 0; m=0 gives a binomial.
Uses ones/(ones+zeros), correcting the denominator in the article pseudocode. -/
@[pl_fold] def polyaEggenberger : Exp rT := pl%
  rec draw n ones zeros reinforcement :=
    if (n < #0) || (ones < #0) || (zeros < #0) || (reinforcement < #0) then fail else
    if n = #0 then #0 else
      if &rationalCoin ones (ones + zeros) then
        #1 + draw (n - #1) (ones + reinforcement) zeros reinforcement
      else draw (n - #1) ones (zeros + reinforcement) reinforcement

/-- Hypergeometric: n draws without replacement from an urn. -/
@[pl_fold] def hypergeometric : Exp rT := pl%
  rec draw n ones zeros :=
    if (n < #0) || (ones < #0) || (zeros < #0) || (ones + zeros < n) then fail else
    if n = #0 then #0 else
      if &rationalCoin ones (ones + zeros) then
        #1 + draw (n - #1) (ones - #1) zeros
      else draw (n - #1) ones (zeros - #1)

/-- Independent symmetric +1 or -1 increments, starting at zero. -/
@[pl_fold] def randomWalk : Exp rT := pl%
  rec walk n := if n < #0 then fail else if n = #0 then #0 else
    let x := walk (n - #1);
    if &fairCoin #() then x + #1 else x - #1

/-- Duchon–Duvignau Poisson(1), as printed under Poisson Distribution.
Uses uniform integers only, without transcendental arithmetic. -/
@[pl_fold] def poissonOne : Exp rT := pl%
  fun u,
    let loop := (rec draw ret a b :=
      let j := &rndInt a;
      if (j < a) && (j < b) then ret else
      if j = a then draw (ret + #1) (a + #1) b
      else draw (ret - #1) (a + #1) (a + #1));
    loop #1 #1 #0

/-- Poisson(x/y) by additivity and binomial thinning of Poisson(1).
Requires x>=0,y>0; uses the article's PoissonInt construction. -/
@[pl_fold] def poissonRational : Exp rT := pl%
  fun x y,
    if (x < #0) || (y <= #0) then fail else if x = #0 then #0 else
      let loop := (rec draw remaining total :=
        if y <= remaining then
          draw (remaining - y) (total + &poissonOne #())
        else if remaining = #0 then total else
          total + &binomial (fun u, &rationalCoin remaining y) (&poissonOne #()));
      loop x #0

end Occil
