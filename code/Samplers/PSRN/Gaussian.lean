import Samplers.PSRN.Uniform

/-!
# Comparison-based Gaussian lazy samplers

Karney's decomposition performs its comparisons on lazy reals and
returns an interval oracle, with rational location and scale transformations.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- Karney's Gaussian selector, with all comparisons performed on lazy reals. -/
@[pl_fold] def gaussianSelector : Exp rT := pl%
  fun k x u,
    let stop := (fun u,
      let category := rand(#2 * k + #2, #());
      if category = #0 then #true else
        if category = #1 then &less x (&newUniform #()) else #false);
    let trial := (rec loop previous n :=
      let z := &newUniform #();
      if &less previous z then n else
        if stop #() then n else loop z (n + #1));
    trial x #0 % #2 = #0

/-- Exact standard normal represented as a lazy interval oracle. This is
Karney's comparison-only decomposition, not a rounded numerical transform. -/
@[pl_fold] def newGaussian : Exp rT := pl%
  fun u,
    let half := (fun u, &expMinusRational #1 #2 #());
    let chooseInteger := (rec draw u :=
      let k := &geometricFailures half #0;
      if &iterateCoin half (k * (k - #1)) then k else draw #());
    let chooseFraction := (rec draw u :=
      let k := chooseInteger #();
      let x := &newUniform #();
      if &iterateCoin (fun u, &gaussianSelector k x #()) (k + #1) then
        &add (&rational k #1) x
      else draw #());
    let x := chooseFraction #();
    if &fairCoin #() then x else &negate x

@[pl_fold] def newNormal : Exp rT := pl%
  fun meanNumerator meanDenominator scaleNumerator scaleDenominator u,
    if (scaleNumerator <= #0) || (scaleDenominator <= #0) then fail else
      &add (&rational meanNumerator meanDenominator)
        (&scaleRational (&newGaussian #()) scaleNumerator scaleDenominator)

end Occil.PSRN
