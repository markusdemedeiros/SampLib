import Samplers.PSRN.Exponential

/-!
# Beta, gamma and gamma-mixture lazy samplers

Shapes and rates use integer numerator/denominator pairs. The existing
constructors retain their stated parameter domains and independent proposals.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- Beta PSRN by Occil's geometric-bag power rejection for a,b>=1.
The integer-shape shortcut uses a+b-1 uniforms (correcting the article typo).
Shapes are positive rational numerator/denominator pairs. Johnk's construction
extends this to two subunit shapes; a power proposal handles mixed shapes. -/
@[pl_fold] def newBeta : Exp rT := pl%
  fun an ad bn bd u,
    if (ad <= #0) || (bd <= #0) || (an <= #0) || (bn <= #0) then fail else
    if (an % ad = #0) && (bn % bd = #0) then
      &newOrderStatistic (an / ad + bn / bd - #1) (an / ad)
    else if bn = bd then &newPowerUniform ad an #() else
    if an = ad then
      &subtract (&rational #1 #1) (&newPowerUniform bd bn #())
    else if (ad <= an) && (bd <= bn) then
      let draw := (rec retry u :=
        let bag := &newUniformBag #();
        let left := &powerCoin (fun u, &sampleGeometricBag bag #()) (an - ad) ad #();
        if left then
          if &powerCoin (fun u, ~(&sampleGeometricBag bag #())) (bn - bd) bd #() then
            &fromUniformBag bag
          else retry #()
        else retry #());
      draw #()
    else if (an < ad) && (bn < bd) then
      let draw := (rec retry u :=
        let x := &newPowerUniform ad an #();
        let y := &newPowerUniform bd bn #();
        let total := &add x y;
        if &less total (&rational #1 #1) then &divide x total else retry #());
      draw #()
    else
      let leftSmall := an < ad;
      let smallNumerator := (if leftSmall then an else bn);
      let smallDenominator := (if leftSmall then ad else bd);
      let bigNumerator := (if leftSmall then bn else an);
      let bigDenominator := (if leftSmall then bd else ad);
      let draw := (rec retry u :=
        let x := &newPowerUniform smallDenominator smallNumerator #();
        let complement := &subtract (&rational #1 #1) x;
        let accept := (fun u, &less (&newUniform #()) complement);
        if &powerCoin accept (bigNumerator - bigDenominator) bigDenominator #() then
          if leftSmall then x else complement
        else retry #());
      draw #()

@[pl_fold] def newGammaInteger : Exp rT := pl%
  rec draw shape rateNumerator rateDenominator :=
    if shape <= #0 then fail else
      let x := &newExponential rateNumerator rateDenominator #();
      if shape = #1 then x else &add x (draw (shape - #1) rateNumerator rateDenominator)

/-- Lindley-like mixture of integer-shape gamma PSRNs at a shared rational rate. -/
@[pl_fold] def newGammaMixture : Exp rT := pl%
  fun weightNumerator weightDenominator shapeA shapeB rateNumerator rateDenominator u,
    if &rationalCoin weightNumerator weightDenominator then
      &newGammaInteger shapeA rateNumerator rateDenominator
    else &newGammaInteger shapeB rateNumerator rateDenominator

@[pl_fold] def newLindley : Exp rT := pl%
  fun numerator denominator u,
    if (numerator <= #0) || (denominator <= #0) then fail else
      &newGammaMixture numerator (numerator + denominator) #1 #2 numerator denominator #()

/-- Gamma with arbitrary positive rational shape and rate. The fractional
shape identity is Gamma(a)=Beta(a,1-a)*Exp(1), followed by gamma additivity. -/
@[pl_fold] def newGamma : Exp rT := pl%
  fun shapeNumerator shapeDenominator rateNumerator rateDenominator u,
    if (shapeNumerator <= #0) || (shapeDenominator <= #0) ||
        (rateNumerator <= #0) || (rateDenominator <= #0) then fail else
      let whole := shapeNumerator / shapeDenominator;
      let remainder := shapeNumerator % shapeDenominator;
      let integerPart := (if whole = #0 then &rational #0 #1 else
        &newGammaInteger whole rateNumerator rateDenominator);
      if remainder = #0 then integerPart else
        let beta := &newBeta remainder shapeDenominator
          (shapeDenominator - remainder) shapeDenominator #();
        let exponential := &newExponential rateNumerator rateDenominator #();
        &add integerPart (&multiply beta exponential)

end Occil.PSRN
