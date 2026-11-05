import Samplers.Discrete.Binomial
import Samplers.Discrete.Counts

/-!
# Compound and multivariate count distributions

Poisson clusters, shared components, category counts, and finite mixtures.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Sum a Poisson number of independent integer-valued jumps. -/
@[pl_fold] def compoundPoisson : Exp rT := pl%
  fun numerator denominator jump,
    let count := &Occil.poissonRational numerator denominator;
    let loop := (rec sum remaining total :=
      if remaining = #0 then total else sum (remaining - #1) (total + jump #()));
    loop count #0

/-- Difference of two independent Poisson random variables. -/
@[pl_fold] def skellam : Exp rT := pl%
  fun leftNumerator leftDenominator rightNumerator rightDenominator,
    let left := &Occil.poissonRational leftNumerator leftDenominator;
    let right := &Occil.poissonRational rightNumerator rightDenominator;
    left - right

/-- Compound Poisson with geometric jumps on 1,2,... (Pólya–Aeppli).
The final two parameters are the geometric jump's success probability. -/
@[pl_fold] def polyaAeppli : Exp rT := pl%
  fun rateNumerator rateDenominator successNumerator successDenominator,
    if successNumerator <= #0 then fail else
      &compoundPoisson rateNumerator rateDenominator
        (fun u, #1 + &Occil.geometric
          (fun u, &Occil.rationalCoin successNumerator successDenominator) #())

/-- Neyman type A: Poisson(delta) independent Poisson(tau) clusters. -/
@[pl_fold] def neymanTypeA : Exp rT := pl%
  fun deltaNumerator deltaDenominator tauNumerator tauDenominator,
    &compoundPoisson deltaNumerator deltaDenominator
      (fun u, &Occil.poissonRational tauNumerator tauDenominator)

/-- Shared-component multivariate Poisson. `otherRates` contains rational pairs. -/
@[pl_fold] def multivariatePoisson : Exp rT := pl%
  fun sharedNumerator sharedDenominator otherRates,
    let shared := &Occil.poissonRational sharedNumerator sharedDenominator;
    let loop := (rec draw rates := case! rates | inl(u) => inl(#()) | inr(p) =>
      let rate := fst(p);
      let n := &Occil.poissonRational (fst(rate)) (snd(rate));
      inr((shared + n, draw (snd(p)))));
    loop otherRates

/-- Counts of each failure category before r successes. Probabilities are
proportional to `successWeight :: failureWeights`; successWeight must be positive. -/
@[pl_fold] def negativeMultinomial : Exp rT := pl%
  fun successes successWeight failureWeights,
    if (successes < #0) || (successWeight <= #0) then fail else
      let valid := (rec check weights := case! weights | inl(u) => #true | inr(p) =>
        if fst(p) < #0 then #false else check (snd(p)));
      if valid failureWeights then
        let weights := inr((successWeight, failureWeights));
        let loop := (rec draw remaining counts := if remaining = #0 then counts else
          let category := &Occil.weightedChoice weights;
          if category = #0 then draw (remaining - #1) counts else
            draw remaining (&incrementCounter counts (category - #1)));
        loop successes (&zeroCounters (&Occil.length failureWeights))
      else fail

/-- CUB/MUB: mixture of a shifted binomial and a discrete uniform on 1..m. -/
@[pl_fold] def cub : Exp rT := pl%
  fun m mixtureNumerator mixtureDenominator biasNumerator biasDenominator,
    if m < #3 then fail else
      if &Occil.rationalCoin mixtureNumerator mixtureDenominator then
        #1 + &binomialBinary (m - #1) (biasDenominator - biasNumerator) biasDenominator
      else #1 + &Occil.uniformInt m

end Occil.DiscreteExtra
