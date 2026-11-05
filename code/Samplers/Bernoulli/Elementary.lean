import Samplers.Bernoulli.Exponential
import Samplers.Bernoulli.Rational

/-!
# Logarithmic, logistic and hyperbolic factories.

Exact callback-coin constructions from Occil’s catalogue. Coin calls and auxiliary random choices are independent.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- (1-p)/(1+p), a uniformly-fast two-coin construction. -/
@[pl_fold] def oneMinusOverOnePlus : Exp rT := pl%
  rec draw coin u :=
    let bit := coin #();
    if &Occil.fairCoin #() then ~bit else
      if bit then #false else draw coin #()

/-- expit(z), where z=a/b may have either sign. -/
@[pl_fold] def sigmoidRational : Exp rT := pl%
  fun a b u,
    if b <= #0 then fail else
      if a < #0 then
        ~(&Occil.oneDivOnePlus (fun u, &Occil.expMinusRational (-a) b #()) #())
      else &Occil.oneDivOnePlus (fun u, &Occil.expMinusRational a b #()) #()

/-- expit((a/b)*p), with arbitrary signed rational a/b. -/
@[pl_fold] def sigmoidScaled : Exp rT := pl%
  fun coin a b u,
    if a < #0 then
      ~(&Occil.oneDivOnePlus (fun u, &expMinusScaled coin (-a) b #()) #())
    else &Occil.oneDivOnePlus (fun u, &expMinusScaled coin a b #()) #()

/-- LogisticExp(z,precision)=1-expit(z/2^precision). -/
@[pl_fold] def logisticExp : Exp rT := pl%
  fun z precision u,
    if precision < #0 then fail else &sigmoidRational (-z) (&intPower #2 precision) #()

/-- tanh(a/b), a>=0,b>0, using exp(-2a/b). -/
@[pl_fold] def tanhRational : Exp rT := pl%
  fun a b u,
    &oneMinusOverOnePlus (fun u, &Occil.expMinusRational (#2 * a) b #()) #()

/-- tanh((a/b)*p), a>=0,b>0. -/
@[pl_fold] def tanhScaled : Exp rT := pl%
  fun coin a b u,
    &oneMinusOverOnePlus (fun u, &expMinusScaled coin (#2 * a) b #()) #()

/-- tanh((m+p)/2), m=a/b>=0. -/
@[pl_fold] def tanhHalfShifted : Exp rT := pl%
  fun coin a b u,
    &oneMinusOverOnePlus (fun u, &expMinusShifted coin a b #()) #()

/-- Exponential shift p*exp(z)/(p*exp(z)+1-p), z=a/b. -/
@[pl_fold] def exponentialTwist : Exp rT := pl%
  rec draw coin a b u :=
    let bit := coin #();
    let select := &sigmoidRational a b #();
    if bit then if select then #true else draw coin a b #()
    else if select then draw coin a b #() else #false

/-- (1+exp(z-w))/(1+exp(z)), z=a/b,w=x/y>=0. -/
@[pl_fold] def exponentialRatio : Exp rT := pl%
  fun a b x y u,
    if &sigmoidRational a b #() then &Occil.expMinusRational x y #() else #true

/-- (1-exp(-(m+p)))/(m+p), with integer m>=0. At m=p=0 return 1. -/
@[pl_fold] def expIntegral : Exp rT := pl%
  fun coin m u,
    if m < #0 then fail else if m = #0 then
      let coefficient := (fun n,
        let factorial := (rec product k := if k <= #1 then #1 else k * product (k - #1));
        (#1, factorial (n + #1)));
      &alternatingSeries coin coefficient #()
    else
      if &expMinusShifted coin m #1 #() then #false else
        &reciprocalAffine coin m #1 #1 #1 #()

/-- ln(c+p)/(c+p), c=a/b>=1, via the one-cycle permutation schema. -/
@[pl_fold] def logOverAffine : Exp rT := pl%
  fun coin a b u,
    if (b <= #0) || (a < b) then fail else
      let count := &Occil.geometric (fun u, &reciprocalAffine coin a b #1 #1 #()) #();
      if count = #0 then #false else &Occil.rationalCoin #1 count

/-- Geometric one-cycle schema: p*ln(1/p), with value zero at p=1.
Requires p>0; the p=0 endpoint does not terminate. -/
@[pl_fold] def pLogInverse : Exp rT := pl%
  fun coin u,
    let failures := &Occil.geometric coin #();
    if failures = #0 then #false else &Occil.rationalCoin #1 failures

/-- (1-p)*ln(1/(1-p)); requires p<1. -/
@[pl_fold] def complementLogInverse : Exp rT := pl%
  fun coin u, &pLogInverse (fun u, ~(coin #())) #()

/-- p/ln(1/(1-p)), extended to one at p=0; p<1. -/
@[pl_fold] def pOverLogInverseComplement : Exp rT := pl%
  fun coin u,
    let bag := &Occil.newUniformBag #();
    &twoCoinPower (fun u, ~(coin #())) (fun u, &Occil.sampleGeometricBag bag #()) #()

/-- (1-p)/ln(1/p), extended to one at p=1; p>0. -/
@[pl_fold] def complementOverLogInverse : Exp rT := pl%
  fun coin u,
    let bag := &Occil.newUniformBag #();
    &twoCoinPower coin (fun u, &Occil.sampleGeometricBag bag #()) #()

/-- Li_r(p)*(1/p-1), integer r>=1, extended to one at p=0. Requires p<1. -/
@[pl_fold] def polylogarithm : Exp rT := pl%
  fun coin order u,
    if order <= #0 then fail else
      let n := &Occil.geometric (fun u, ~(coin #())) #() + #1;
      &Occil.rationalCoin #1 (&intPower n order)

/-- (1+p)/2. -/
@[pl_fold] def onePlusHalf : Exp rT := pl%
  fun coin u, if &Occil.fairCoin #() then #true else coin #()

/-- (1-p)/2. -/
@[pl_fold] def complementHalf : Exp rT := pl%
  fun coin u, if &Occil.fairCoin #() then #false else ~(coin #())

/-- 1-ln(1+p). -/
@[pl_fold] def complementLogOnePlus : Exp rT := pl%
  fun coin u, ~(&Occil.logOnePlusFactory coin #())

/-- expit(z)*(1-expit(z)), z=a/b. -/
@[pl_fold] def sigmoidDerivative : Exp rT := pl%
  fun a b u,
    if &sigmoidRational a b #() then ~(&sigmoidRational a b #()) else #false

end Occil.FactoryExtra
