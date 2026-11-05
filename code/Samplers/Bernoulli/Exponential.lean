import Samplers.Bernoulli.Series
import Samplers.Bernoulli.Combinators
import Samplers.Constants

/-!
# Exponential and binary-exponential factories.

These constructions transform abstract input coins without evaluating their unknown probabilities.
-/
namespace Occil.FactoryExtra

open ProbLang

variable {rT : Type _}

/-- exp(-c*p), c=a/b>=0, by Poisson thinning. -/
@[pl_fold] def expMinusScaled : Exp rT := pl%
  fun coin a b u,
    let n := &Occil.poissonRational a b;
    &Occil.iterateCoin (fun u, ~(coin #())) n

/-- exp(-m-p), where m=a/b>=0. -/
@[pl_fold] def expMinusShifted : Exp rT := pl%
  fun coin a b u,
    if &Occil.expMinusRational a b #() then &Occil.expMinusMartingale coin #() else #false

/-- exp(p)*(1-p), the sorted-uniform von Neumann schema. -/
@[pl_fold] def expTimesComplement : Exp rT := pl%
  fun coin u,
    let loop := (rec draw n previous :=
      if coin #() then
        let x := urand;
        if n = #0 then draw #1 x else
          if previous < x then #false else draw (n + #1) x
      else #true);
    loop #0 (toReal(#0))

/-- exp(-sum_i a_i*p^i), nonnegative rational coefficient pairs a_i. -/
@[pl_fold] def expMinusPolynomial : Exp rT := pl%
  fun coin coefficients u,
    let loop := (rec product remaining degree :=
      case! remaining
        | inl(v) => #true
        | inr(pair) =>
          let coefficient := fst(pair);
          if &expMinusScaled (fun u, &Occil.iterateCoin coin degree)
              (fst(coefficient)) (snd(coefficient)) #()
          then product (snd(pair)) (degree + #1) else #false);
    loop coefficients #0

/-- exp(-(m+p)^k), integer m,k>=0, via its binomial polynomial expansion. -/
@[pl_fold] def expMinusShiftPower : Exp rT := pl%
  fun coin m k u,
    if (m < #0) || (k < #0) then fail else
      let loop := (rec product i :=
        if k < i then #true else
          let repetitions := &choose k i * &intPower m (k - i);
          if &Occil.iterateCoin
              (fun u, &Occil.expMinusMartingale (fun u, &Occil.iterateCoin coin i) #())
              repetitions
          then product (i + #1) else #false);
      loop #0

/-- exp(p)/3, from Poisson generating functions and the known e/3 coin. -/
@[pl_fold] def expDivThree : Exp rT := pl%
  fun coin u,
    if &Occil.Constants.eDivThree #() then
      &Occil.probabilityGeneratingFactory coin (fun u, &Occil.poissonOne #()) #()
    else #false

/-- exp(-exp(m+p)), integer m>=0; Poisson thinning from the source recipe. -/
@[pl_fold] def expMinusExp : Exp rT := pl%
  fun coin m u,
    if m < #0 then fail else
      let count := &Occil.poissonRational (&intPower #3 (m + #1)) #1;
      let trial := (fun u,
        if &Occil.iterateCoin &Occil.Constants.eDivThree m then &expDivThree coin #()
        else #false);
      &Occil.iterateCoin (fun u, ~(trial #())) count

/-- exp(p^2)*(1-p), the factorial-pair alternating-series construction. -/
@[pl_fold] def expSquareTimesComplement : Exp rT := pl%
  fun coin u,
    let factorial := (rec product n := if n <= #1 then #1 else n * product (n - #1));
    &alternatingSeries coin (fun n, (#1, factorial (n / #2))) #()

/-- 2^(-m*(k+p)), integers m,k>=0. The exact ln(2)-coin avoids computing ln(2). -/
@[pl_fold] def binaryExponential : Exp rT := pl%
  fun coin m k u,
    if (m < #0) || (k < #0) then fail else
      if &Occil.rationalCoin #1 (&intPower #2 (m * k)) then
        &expMinusScaled (fun u,
          if coin #() then &Occil.Constants.logOnePlusRational #1 #1 #() else #false)
          m #1 #()
      else #false

/-- 2^(-(a/b)*p), a>=0,b>0. -/
@[pl_fold] def binaryExponentialRational : Exp rT := pl%
  fun coin a b u,
    &expMinusScaled (fun u,
      if coin #() then &Occil.Constants.logOnePlusRational #1 #1 #() else #false)
      a b #()

end Occil.FactoryExtra
