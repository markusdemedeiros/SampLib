import Samplers.Discrete.Compound
import Samplers.Numerical

/-!
# Numerical parameters for discrete mixture distributions

Every real parameter is a signed integer on the explicit fixed-point scale.
The output is an ordinary integer count, not a fixed-point number. The random
mixture parameter is numerical; conditional integer sampling remains exact.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- Negative binomial with a positive numerical shape and success probability,
using the gamma–Poisson mixture. Shape need not be an integer. -/
@[pl_fold] def negativeBinomialNumerical : Exp rT := pl%
  fun scale shape successProbability u,
    if (scale <= #0) || (shape <= #0) || (successProbability <= #0) ||
       (scale < successProbability)
    then fail else if successProbability = scale then #0 else
      let rate := &Numeric.div scale successProbability (scale - successProbability);
      let intensity := &Numerical.gamma scale shape rate #();
      &Occil.poissonRational intensity scale

/-- Beta-negative-binomial with arbitrary numerical beta shapes and an integer
success count. A beta value that rounds to zero is redrawn to avoid a spurious
nonterminating geometric trial on the numerical grid. -/
@[pl_fold] def betaNegativeBinomialNumerical : Exp rT := pl%
  rec draw scale successes alpha beta u :=
    if (successes < #0) || (alpha <= #0) || (beta <= #0) then fail else
    if successes = #0 then #0 else
      let probability := &Numerical.beta scale alpha beta #();
      if probability <= #0 then draw scale successes alpha beta #() else
        &Occil.negativeBinomial (fun u, &Numeric.coin scale probability #()) successes

/-- Bell–Touchard(a,b): sum Poisson(b*(exp(a)-1)) positive Poisson(a) clusters.
Both a and b are positive numerical real parameters. -/
@[pl_fold] def bellTouchard : Exp rT := pl%
  fun scale a b u,
    if (scale <= #0) || (a <= #0) || (b <= #0) then fail else
      let intensity := &Numeric.mul scale b (&Numeric.exp scale a - scale);
      &compoundPoisson intensity scale (fun u, &zeroTruncatedPoisson a scale)

/-- The standard one-parameter Bell distribution: Bell–Touchard(a,1).
The site's table prints b=0, which would make its preceding construction
identically zero; this term uses the conventional nondegenerate b=1 case. -/
@[pl_fold] def bell : Exp rT := pl%
  fun scale a u, &bellTouchard scale a scale #()

/-- Discrete Pareto(delta,p), supported on 1,2,..., by the gamma mixture
in `randmisc.html`. Rounds of zero success probability are redrawn. -/
@[pl_fold] def discretePareto : Exp rT := pl%
  rec draw scale delta probability u :=
    if (scale <= #0) || (delta <= #0) || (probability <= #0) ||
       (scale <= probability)
    then fail else
      let shape := &Numeric.div scale scale delta;
      let gamma := &Numerical.gamma scale shape scale #();
      let factor := -(&Numeric.mul scale delta (&Numeric.log scale (scale - probability)));
      let intensity := &Numeric.mul scale gamma factor;
      let success := scale - &Numeric.exp scale (-intensity);
      if success <= #0 then draw scale delta probability #() else
        #1 + &Occil.geometric (fun u, &Numeric.coin scale success #()) #()

end Occil.DiscreteExtra
