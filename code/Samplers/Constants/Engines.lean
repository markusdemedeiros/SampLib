import Samplers.Lazy

/-!
# Exact known-probability coin engines

Digits, rational bounds, converging series and algebraic signs describe a fixed
constant. Callbacks supply that description, not a coin for the target law.
Sources: Occil's Bernoulli Factory Algorithms, constant-generation sections.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

/-- Bernoulli(0.d₁d₂...) in the supplied base. `digit k` is an integer in
[0,base), indexed from one. Infinite all-zero/all-maximal expansions are allowed. -/
@[pl_fold] def fromDigits : Exp rT := pl%
  fun base digit u,
    if base < #2 then fail else
      let compare := (rec read k :=
        let d := digit k;
        if (d < #0) || (base <= d) then fail else
          let v := &Occil.uniformInt base;
          if v < d then #true else if d < v then #false else read (k + #1));
      compare #1

/-- Occil's digit-expansion algorithm when `approx k` approximates p by pk/base^k,
with absolute error at most base^(-k). Returns Bernoulli(p) without fixed precision. -/
@[pl_fold] def fromApproximateDigits : Exp rT := pl%
  fun base approx u,
    if base < #2 then fail else
      let compare := (rec read k digits :=
        let v := &Occil.uniformInt base;
        let next := digits * base + v;
        let pk := approx k;
        if pk + #1 <= next then #false else
        if next <= pk - #2 then #true else read (k + #1) next);
      compare #1 #0

/-- `bounds n` returns (lower,(upper,denominator)), enclosing one fixed p in [0,1].
The interval widths must tend to zero. One shared lazy uniform is compared with
all bounds; no resampling of the latent comparison value occurs. -/
@[pl_fold] def fromBounds : Exp rT := pl%
  fun bounds u,
    let bag := &Occil.newUniformBag #();
    let decide := (rec refine n :=
      let interval := bounds n;
      let lower := (fst(interval));
      let upper := fst(snd(interval));
      let denominator := snd(snd(interval));
      if (denominator <= #0) || (upper < lower) then fail else
      if &Occil.uniformBagLess bag lower denominator then #true else
      if &Occil.uniformBagLess bag upper denominator then refine (n + #1) else #false);
    decide #0

/-- Positive rational series. `term n` returns (a,(b,(errorNumerator,errorDenominator)))
for the next a/b and a certified upper bound on the remaining sum. -/
@[pl_fold] def fromPositiveSeries : Exp rT := pl%
  fun term u,
    let bag := &Occil.newUniformBag #();
    let decide := (rec refine n numerator denominator :=
      let specification := term n;
      let a := (fst(specification));
      let b := fst(snd(specification));
      let error := snd(snd(specification));
      let errorNumerator := (fst(error));
      let errorDenominator := (snd(error));
      if (a < #0) || (b <= #0) || (errorNumerator < #0) ||
          (errorDenominator <= #0) then fail else
        let nextNumerator := numerator * b + a * denominator;
        let nextDenominator := denominator * b;
        if &Occil.uniformBagLess bag nextNumerator nextDenominator then #true else
          let upperNumerator := nextNumerator * errorDenominator + errorNumerator * nextDenominator;
          let upperDenominator := nextDenominator * errorDenominator;
          if &Occil.uniformBagLess bag upperNumerator upperDenominator then
            refine (n + #1) nextNumerator nextDenominator
          else #false);
    decide #0 #0 #1

/-- Positive generalized continued fraction b₁/(a₁+b₂/(a₂+...)).
`coefficient i` returns (b,(a,last)); integer 0<b<=a, indexed from one.
This is Occil's repeated two-coin Algorithm 3, including finite final coefficients. -/
@[pl_fold] def generalizedContinuedFraction : Exp rT := pl%
  rec draw coefficient position :=
    let entry := coefficient position;
    let b := (fst(entry));
    let a := fst(snd(entry));
    let last := snd(snd(entry));
    if (b <= #0) || (a < b) then fail else
    if last then &Occil.rationalCoin b a else
      if &Occil.rationalCoin a (a + #1) then &Occil.rationalCoin b a else
      if draw coefficient (position + #1) then #false else draw coefficient position

/-- Positive rational generalized continued fractions. Each callback entry is
(b,(a,(d,last))), representing numerator b/d and denominator a/d with 0<b<=a.
This preserves the rational size of a_i, not just the ratio b_i/a_i. -/
@[pl_fold] def rationalContinuedFraction : Exp rT := pl%
  rec draw coefficient position :=
    let entry := coefficient position;
    let b := fst(entry);
    let a := fst(snd(entry));
    let specification := snd(snd(entry));
    let d := fst(specification);
    let last := snd(specification);
    if (b <= #0) || (a < b) || (d <= #0) then fail else
    if last then &Occil.rationalCoin b a else
      if &Occil.rationalCoin a (a + d) then &Occil.rationalCoin b a else
      if draw coefficient (position + #1) then #false else draw coefficient position

/-- Positive simple continued fractions. `coefficient i` returns (a,last). -/
@[pl_fold] def continuedFraction : Exp rT := pl%
  fun coefficient u,
    &generalizedContinuedFraction (fun i, (#1, coefficient i)) #1

/-- Continued logarithm: (1/2^c₁)/(1+(1/2^c₂)/(1+...)).
`coefficient i` returns (c,last), c a nonnegative integer. -/
@[pl_fold] def continuedLogarithm : Exp rT := pl%
  rec draw coefficient position :=
    let entry := coefficient position;
    let exponent := (fst(entry));
    if exponent < #0 then fail else
      let power := (rec twice n value := if n = #0 then value else twice (n - #1) (value * #2));
      let denominator := power exponent #1;
      if (snd(entry)) then &Occil.rationalCoin #1 denominator else
      if &Occil.fairCoin #() then &Occil.rationalCoin #1 denominator else
      if draw coefficient (position + #1) then #false else draw coefficient position

/-- Bernoulli at a unique sign-changing root in (0,1). `sign n d` returns
-1, 0 or 1 for the polynomial at n/d. Endpoints must have opposite signs.
An exact dyadic root returns the current random bit's comparison immediately. -/
@[pl_fold] def algebraicRoot : Exp rT := pl%
  fun sign u,
    let atZero := sign #0 #1;
    let atOne := sign #1 #1;
    if (atZero = #0) || (atOne = #0) || (atZero = atOne) then fail else
      let decide := (rec refine digits denominator :=
        let bit := &Occil.uniformInt #2;
        let numerator := #2 * digits + #1;
        let atMiddle := sign numerator denominator;
        if atMiddle = #0 then bit = #0 else
        if bit = #1 then
          if atMiddle = atZero then refine (#2 * digits + bit) (#2 * denominator) else #false
        else if atMiddle = atZero then #true
        else refine (#2 * digits + bit) (#2 * denominator));
      decide #0 #2

end Occil.Constants
