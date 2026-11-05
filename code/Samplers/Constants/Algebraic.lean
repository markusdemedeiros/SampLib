import Samplers.Constants.Engines

/-!
# Algebraic probability constants

Golden-ratio and square-root coins use exact rational sign tests through the
algebraic-root engine. Random decisions and arithmetic remain in ProbLang.
-/
namespace Occil.Constants

open ProbLang

variable {rT : Type _}

@[pl_fold] def integerSign : Exp rT := pl%
  fun x, if x < #0 then #(-1) else if x = #0 then #0 else #1

/-- Exact inverse golden ratio, root of 1-x-x². -/
@[pl_fold] def inverseGoldenRatio : Exp rT := pl%
  fun u, &algebraicRoot (fun n d, &integerSign (d * d - n * d - n * n)) #()

@[pl_fold] def sqrtTwoMinusOne : Exp rT := pl%
  fun u, &algebraicRoot (fun n d, &integerSign (n * n + #2 * n * d - d * d)) #()

@[pl_fold] def inverseSqrtTwo : Exp rT := pl%
  fun u, &algebraicRoot (fun n d, &integerSign (#2 * n * n - d * d)) #()

/-- Exact G(m,ell)^(-k), G=(m+sqrt(m²+4ell))/2>1. This uses the
algebraic-root construction rather than the specialized Fibonacci expansion. -/
@[pl_fold] def goldenFamily : Exp rT := pl%
  fun m ell k u,
    if (m <= #0) || (k < #0) then fail else
    if ((ell = #1) || (ell = #(-1))) then
      if (ell = #(-1)) && (m < #3) then fail else
        let root := (fun v, &algebraicRoot (fun n d,
          &integerSign (ell * n * n + m * n * d - d * d)) #());
        let repeatCoin := (rec draw remaining := if remaining = #0 then #true else
          if root #() then draw (remaining - #1) else #false);
        repeatCoin k
    else fail

end Occil.Constants
