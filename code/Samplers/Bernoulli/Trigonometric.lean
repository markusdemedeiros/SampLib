import Samplers.Bernoulli.Series
import Samplers.Bernoulli.Linear
import Samplers.Constants

/-!
# Trigonometric factories and permutation schemas.

These terms simulate trigonometric probabilities using exact series, permutation laws and known-constant coins.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- sin(p*sqrt(c))/(p*sqrt(c)), c=a/b in (0,6], extended to one at p=0. -/
@[pl_fold] def sincScaled : Exp rT := pl%
  fun coin a b u,
    if (a <= #0) || (b <= #0) || (#6 * b < a) then fail else
      let factorial := (rec product n := if n <= #1 then #1 else n * product (n - #1));
      let coefficient := (fun n,
        (&intPower a n, &intPower b n * factorial (#2 * n + #1)));
      &alternatingSeries (fun u, &Occil.iterateCoin coin #2) coefficient #()

/-- cos(sqrt(p)), an alternating power-series factory. -/
@[pl_fold] def cosineSqrt : Exp rT := pl%
  fun coin u,
    let factorial := (rec product n := if n <= #1 then #1 else n * product (n - #1));
    &alternatingSeries coin (fun n, (#1, factorial (#2 * n))) #()

/-- arctan(p)/pi, with the exact known inverse-pi coin. -/
@[pl_fold] def arctanOverPi : Exp rT := pl%
  fun coin u,
    if &Occil.Constants.inversePi #() then &Occil.arctanFactory coin #() else #false

/-- sin(sqrt(c*p))/sqrt(c*p), c=a/b in (0,6]. -/
@[pl_fold] def sincSqrtScaled : Exp rT := pl%
  fun coin a b u,
    if (a <= #0) || (b <= #0) || (#6 * b < a) then fail else
      let factorial := (rec product n := if n <= #1 then #1 else n * product (n - #1));
      let coefficient := (fun n,
        (&intPower a n, &intPower b n * factorial (#2 * n + #1)));
      &alternatingSeries coin coefficient #()

/-- Sorted-alternating permutation schema. parity=0 returns (1-p)/cos(p),
parity=1 returns (1-p)*tan(p). Requires p<1. -/
@[pl_fold] def alternatingPermutation : Exp rT := pl%
  fun coin parity u,
    let count := &Occil.geometric (fun u, ~(coin #())) #();
    if count % #2 = parity then
      let previous := urand;
      let loop := (rec draw i last :=
        if count <= i then #true else
          let next := urand;
          if i % #2 = #1 then
            if next < last then #false else draw (i + #1) next
          else if last < next then #false else draw (i + #1) next);
      loop #1 previous
    else #false

@[pl_fold] def complementOverCosine : Exp rT := pl%
  fun coin u, &alternatingPermutation coin #0 #()

@[pl_fold] def complementTimesTangent : Exp rT := pl%
  fun coin u, &alternatingPermutation coin #1 #()

/-- arcsin(p)+sqrt(1-p^2)-1. The factored series f(p)/p has decreasing
alternating coefficient magnitudes, and an outer p-coin restores f(p). -/
@[pl_fold] def arcsinePlusSqrtMinusOne : Exp rT := pl%
  fun coin u,
    if coin #() then
      let coefficient := (fun n,
        let degree := n + #1;
        let k := degree / #2;
        let factor := (if degree % #2 = #1 then degree else degree - #1);
        (&choose (#2 * k) k, &intPower #4 k * factor));
      &alternatingSeries coin coefficient #()
    else #false

/-- arcsin(p)/2, by cancelling the square-root component. -/
@[pl_fold] def arcsineHalf : Exp rT := pl%
  fun coin u,
    if &Occil.fairCoin #() then &arcsinePlusSqrtMinusOne coin #() else
      ~(&Occil.fractionalPower (fun u, ~(&Occil.iterateCoin coin #2)) #1 #2 #())

/-- p/tan(p), with an explicit valid lower bound e/f on sin(p)-p*cos(p).
The bound is strictly positive, so this formulation requires p>0. -/
@[pl_fold] def pOverTangent : Exp rT := pl%
  fun coin e f u,
    let numerator := (fun u,
      if coin #() then &Occil.cosineFactory coin #() else #false);
    &division numerator (fun u, &Occil.sineFactory coin #()) e f #()

end Occil.FactoryExtra
