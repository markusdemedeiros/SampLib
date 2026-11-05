import Samplers.Continuous
import Samplers.Discrete

/-! Coin composition, logistic transformation, and polynomial selection. -/
namespace Occil

open ProbLang

variable {rT : Type _}

/-- Rational scaled logistic factory cp/(1+cp), c=x/y>0. -/
@[pl_fold] def logisticFactory : Exp rT := pl%
  rec draw coin x y u :=
    if (x <= #0) || (y <= #0) then fail else
      if &rationalCoin y (x + y) then #false else
      if coin #() then #true else draw coin x y #()

/-- Probability generating function E[p^N] for a nonnegative integer sampler. -/
@[pl_fold] def probabilityGeneratingFactory : Exp rT := pl%
  fun coin integerSampler u,
    let n := integerSampler #();
    if n < #0 then fail else &iterateCoin coin n

/-- Polynomial in Bernstein form: flip n times, then select coefficient #heads.
Coefficients are rational (numerator,denominator) pairs. -/
@[pl_fold] def bernsteinFactory : Exp rT := pl%
  fun coin coefficients u,
    let n := &length coefficients - #1;
    if n < #0 then fail else
      let heads := &binomial coin n;
      let coefficient := &getAt coefficients heads;
      &rationalCoin (fst(coefficient)) (snd(coefficient))

end Occil
