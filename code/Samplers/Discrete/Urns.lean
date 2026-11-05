import Samplers.Discrete.Binomial

/-!
# Exact urn distributions

Central and noncentral sampling, reinforced beta mixtures, and multicolor urns.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Wallenius noncentral hypergeometric, by weighted sampling without replacement.
The odds of drawing a one relative to a zero are oddsNumerator/oddsDenominator. -/
@[pl_fold] def walleniusHypergeometric : Exp rT := pl%
  rec draw n ones zeros oddsNumerator oddsDenominator :=
    if (n < #0) || (ones < #0) || (zeros < #0) || (ones + zeros < n) ||
       (oddsNumerator <= #0) || (oddsDenominator <= #0)
    then fail else if n = #0 then #0 else
      if &Occil.rationalCoin (ones * oddsNumerator)
          (ones * oddsNumerator + zeros * oddsDenominator) then
        #1 + draw (n - #1) (ones - #1) zeros oddsNumerator oddsDenominator
      else draw (n - #1) ones (zeros - #1) oddsNumerator oddsDenominator

/-- Fisher noncentral hypergeometric, by its exact finite integer-weight table. -/
@[pl_fold] def fisherHypergeometric : Exp rT := pl%
  fun n ones zeros oddsNumerator oddsDenominator,
    if (n < #0) || (ones < #0) || (zeros < #0) || (ones + zeros < n) ||
       (oddsNumerator <= #0) || (oddsDenominator <= #0)
    then fail else
      let weights := (rec build k := if n < k then inl(#()) else
        let w := &choose ones k * &choose zeros (n - k) *
          &integerPower oddsNumerator k * &integerPower oddsDenominator (n - k);
        inr((w, build (k + #1))));
      &Occil.weightedChoice (weights #0)

/-- Negative hypergeometric: failures before r successes without replacement. -/
@[pl_fold] def negativeHypergeometric : Exp rT := pl%
  rec draw successes ones zeros :=
    if (successes < #0) || (ones < successes) || (zeros < #0) then fail else
    if successes = #0 then #0 else
      if &Occil.rationalCoin ones (ones + zeros) then
        draw (successes - #1) (ones - #1) zeros
      else #1 + draw successes ones (zeros - #1)

/-- Beta-binomial with positive rational beta shapes, using a reinforced urn. -/
@[pl_fold] def betaBinomial : Exp rT := pl%
  fun trials alphaNumerator alphaDenominator betaNumerator betaDenominator,
    if (alphaNumerator <= #0) || (alphaDenominator <= #0) ||
       (betaNumerator <= #0) || (betaDenominator <= #0)
    then fail else
      &Occil.polyaEggenberger trials (alphaNumerator * betaDenominator)
        (betaNumerator * alphaDenominator) (alphaDenominator * betaDenominator)

/-- Change one integer counter by an integer delta. -/
@[pl_fold] def adjustCounter : Exp rT := pl%
  rec adjust counters index delta := case! counters
    | inl(u) => fail
    | inr(p) => if index = #0 then inr((fst(p) + delta, snd(p))) else
        inr((fst(p), adjust (snd(p)) (index - #1) delta))

/-- Validate equally sized nonnegative counts and strictly positive integer odds. -/
@[pl_fold] def validUrn : Exp rT := pl%
  rec check counts odds := case! counts
    | inl(u) => (case! odds | inl(v) => #true | inr(q) => #false)
    | inr(p) => (case! odds | inl(v) => #false | inr(q) =>
        if ((fst(p)) < #0) || ((fst(q)) <= #0) then #false
        else check (snd(p)) (snd(q)))

/-- Products of corresponding count and odds entries. -/
@[pl_fold] def urnWeights : Exp rT := pl%
  rec build counts odds := case! counts
    | inl(u) => inl(#())
    | inr(p) => (case! odds | inl(v) => fail | inr(q) =>
        inr((fst(p) * fst(q), build (snd(p)) (snd(q)))))

/-- Multicolor Wallenius urn with positive integer odds, returned as color counts. -/
@[pl_fold] def walleniusMultivariate : Exp rT := pl%
  fun draws counts odds,
    if (draws < #0) || (&Occil.sumInts counts < draws) then fail else
    if &validUrn counts odds then
      let loop := (rec take remaining population result :=
        if remaining = #0 then result else
          let color := &Occil.weightedChoice (&urnWeights population odds);
          take (remaining - #1) (&adjustCounter population color (-#1))
            (&incrementCounter result color));
      loop draws counts (&zeroCounters (&Occil.length counts))
    else fail

/-- Multivariate hypergeometric is the equal-odds multicolor urn. -/
@[pl_fold] def multivariateHypergeometric : Exp rT := pl%
  fun draws counts,
    let ones := (rec build xs := case! xs | inl(u) => inl(#()) | inr(p) =>
      inr((#1, build (snd(p)))));
    &walleniusMultivariate draws counts (ones counts)

/-- Multicolor Fisher noncentral hypergeometric by independent binomials
conditioned on their total. Positive integer odds; exact but rejection can be slow. -/
@[pl_fold] def fisherMultivariate : Exp rT := pl%
  fun draws counts odds,
    let total := &Occil.sumInts counts;
    if (draws < #0) || (total < draws) then fail else
    if &validUrn counts odds then
      if draws = #0 then &zeroCounters (&Occil.length counts) else
      if draws = total then counts else
        let proposals := (rec build population weights := case! population
          | inl(u) => inl(#())
          | inr(p) => (case! weights | inl(v) => fail | inr(q) =>
              let count := &binomialBinary (fst(p)) (fst(q)) (fst(q) + #1);
              inr((count, build (snd(p)) (snd(q))))));
        let loop := (rec draw u :=
          let values := proposals counts odds;
          if &Occil.sumInts values = draws then values else draw #());
        loop #()
    else fail

end Occil.DiscreteExtra
