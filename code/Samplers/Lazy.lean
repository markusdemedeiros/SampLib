import Samplers.Factories

/-! Uniform random bit streams / geometric bags from exporand.html and
bernoulli.py. The heap memoizes each digit. These are observable finite operations
on a lazy uniform, not eager construction of an infinite real. -/
namespace Occil
open ProbLang
variable {rT : Type _}

/-- A lazy node is unsampled nil, or cons(bit,next node). -/
@[pl_fold] def newUniformBag : Exp rT := pl% fun u, alloc(inl(#()))

/-- Read and cache one bit and the remaining stream. -/
@[pl_fold] def uniformBagStep : Exp rT := pl%
  fun bag,
    case! !bag
      | inl(u) =>
        let tail := &newUniformBag #();
        let bit := &fairCoin #();
        let p := (bit, tail);
        bag ← inr(p);
        p
      | inr(p) => p

/-- First n bits as an integer in [0,2^n); rereading the same prefix is stable. -/
@[pl_fold] def uniformBagPrefix : Exp rT := pl%
  fun bag n,
    if n < #0 then fail else
      let loop := (rec read node remaining acc :=
        if remaining = #0 then acc else
          let p := &uniformBagStep node;
          let bit := (if (fst(p)) then #1 else #0);
          read ((snd(p))) (remaining - #1) (acc * #2 + bit));
      loop bag n #0

/-- Compare the represented U with a rational x/y, with exact integer arithmetic.
Requires y>0; rationals outside the unit interval are handled by saturation. -/
@[pl_fold] def uniformBagLess : Exp rT := pl%
  rec compare bag x y :=
    if y <= #0 then fail else
    if x <= #0 then #false else if y <= x then #true else
      let p := &uniformBagStep bag;
      let twice := #2 * x;
      if (fst(p)) then
        if twice < y then #false else compare ((snd(p))) (twice - y) y
      else if twice < y then compare ((snd(p))) twice y else #true

/-- Draw Bernoulli(U) from a shared uniform bag: choose a geometrically
located digit. Multiple calls are conditionally independent given U, not
unconditionally independent (the shared latent probability is intentional). -/
@[pl_fold] def sampleGeometricBag : Exp rT := pl%
  rec choose bag u :=
    let p := &uniformBagStep bag;
    if &fairCoin #() then (fst(p)) else choose ((snd(p))) #()

/-- Alternating factorial-series factory. mode=0: exp(-p), mode=1: cos(p),
mode=2: sin(p)/p, extended to 1 at p=0. Bounds are exact integer fractions
with a common factorial denominator; one cached uniform is reused throughout.
This follows the exp_minus/cos/sin martingale algorithms in bernoulli.py. -/
@[pl_fold] def factorialSeriesFactory : Exp rT := pl%
  fun coin mode u,
    if (mode < #0) || (#2 < mode) then fail else
      let bag := &newUniformBag #();
      let fac := (if mode = #0 then #1 else if mode = #1 then #2 else #6);
      let loop := (rec draw n denominator lower upper weight :=
        let nextWeight := (if weight then
          if coin #() then if mode = #0 then #true else coin #() else #false
          else #false);
        let term := (if nextWeight then #1 else #0);
        let lo := (if n % #2 = #1 then upper - term else lower);
        let hi := (if n % #2 = #0 then lower + term else upper);
        if &uniformBagLess bag lo denominator then #true else
        if &uniformBagLess bag hi denominator then
          let factor := (if mode = #0 then n + #1 else
            if mode = #1 then (#2 * n + #1) * (#2 * n + #2)
            else (#2 * n + #2) * (#2 * n + #3));
          draw (n + #1) (denominator * factor) (lo * factor) (hi * factor) nextWeight
        else #false);
      loop #1 fac #0 fac #true

@[pl_fold] def expMinusMartingale : Exp rT := pl%
  fun coin u, &factorialSeriesFactory coin #0 #()

@[pl_fold] def cosineFactory : Exp rT := pl%
  fun coin u, &factorialSeriesFactory coin #1 #()

@[pl_fold] def sineFactory : Exp rT := pl%
  fun coin u, if coin #() then &factorialSeriesFactory coin #2 #() else #false

/-- ln(1+p). The outer p-coin is needed: averaging 1/(1+pU) alone gives
ln(1+p)/p, not ln(1+p). The Python helper's docstring obscures this distinction. -/
@[pl_fold] def logOnePlusFactory : Exp rT := pl%
  fun coin u,
    if coin #() then
      let bag := &newUniformBag #();
      &oneDivOnePlus (fun u,
        if coin #() then &sampleGeometricBag bag #() else #false) #()
    else #false

/-- arctan(p)/p, continuously extended to 1 at p=0. -/
@[pl_fold] def arctanOverPFactory : Exp rT := pl%
  fun coin u,
    let bag := &newUniformBag #();
    &oneDivOnePlus (fun u,
      if coin #() then if coin #() then
        if &sampleGeometricBag bag #() then &sampleGeometricBag bag #() else #false
      else #false else #false) #()

@[pl_fold] def arctanFactory : Exp rT := pl%
  fun coin u, if coin #() then &arctanOverPFactory coin #() else #false

end Occil
