import Samplers.FactoryExtra
import Samplers.Constants
import Metrology.ProbLang.Interp.BigStepIO

/-! Closed interpreter fixtures for exact Bernoulli factories and constant coins.
Callbacks carry their stated distributions; no runtime sampling occurs in Lean.
Numerical fixtures use Q(2^20), and have names that identify the approximation. -/
namespace WideExtras

open ProbLang

private def scale : Int := 1048576
private def q (a : Int) (b : Int := 1) : Int := scale * a / b
private def ints (xs : List Int) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.int x)) tail)) (.inl (.lit .unit))
private def fractions (xs : List (Int × Int)) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair
    (.pair (.lit (.int x.1)) (.lit (.int x.2))) tail)) (.inl (.lit .unit))
private def p : Exp Float := pl% fun u, &Occil.rationalCoin #3 #10
private def r : Exp Float := pl% fun u, &Occil.rationalCoin #1 #5
private def h : Exp Float := pl% fun u, &Occil.rationalCoin #3 #5

/-- These names are intentionally separate from ordinary numerical distribution fixtures. -/
def factoryCases : List (String × Exp Float) := [
  ("factory_power", pl(&Occil.FactoryExtra.rationalPower &p #7 #3 #())),
  ("factory_two_power", pl(&Occil.FactoryExtra.twoCoinPower &p &r #())),
  ("factory_two_coin", pl(&Occil.FactoryExtra.twoCoin &p &r #2 #3 #3 #4 #())),
  ("factory_linear", pl(&Occil.FactoryExtra.linear &p #2 #1 #1 #4 #())),
  ("factory_linear_power", pl(&Occil.FactoryExtra.linearPower &p #2 #1 #2 #1 #4 #())),
  ("factory_addition", pl(&Occil.FactoryExtra.addition &p &r #1 #4 #())),
  ("factory_subtraction", pl(&Occil.FactoryExtra.subtraction &h &r #1 #4 #())),
  ("factory_division", pl(&Occil.FactoryExtra.division &r &h #1 #4 #())),
  ("factory_epsilon_division", pl(&Occil.FactoryExtra.epsilonDivision &h #1 #5 #1 #2 #())),
  ("factory_reciprocal_affine", pl(&Occil.FactoryExtra.reciprocalAffine &p #2 #1 #1 #1 #())),
  ("factory_affine", pl(&Occil.FactoryExtra.affine &p #2 #1 #1 #2 #1 #4 #())),
  ("factory_affine_ratio", pl(&Occil.FactoryExtra.affineRatio &h &r #1 #1 #1 #5 #1 #4 #())),
  ("factory_reciprocal_logistic", pl(&Occil.FactoryExtra.reciprocalLogistic &p #3 #2 #())),
  ("factory_two_minus", pl(&Occil.FactoryExtra.oneDivTwoMinus &p #())),
  ("factory_exp_scaled", pl(&Occil.FactoryExtra.expMinusScaled &p #5 #2 #())),
  ("factory_exp_shifted", pl(&Occil.FactoryExtra.expMinusShifted &p #1 #2 #())),
  ("factory_exp_complement", pl(&Occil.FactoryExtra.expTimesComplement &p #())),
  ("factory_alternating", pl(&Occil.FactoryExtra.alternatingSeries &p
    (fun n, (#1, n + #1)) #())),
  ("factory_positive_series", pl(&Occil.FactoryExtra.positivePowerSeries &p &(ints [1, 2, 3]) #())),
  ("factory_complement_series", pl(&Occil.FactoryExtra.complementPowerSeries &p &(ints [1, 2, 3]) #())),
  ("factory_hazards", pl(&Occil.FactoryExtra.powerSeriesHazards &p (fun n, (#1, #2)) #())),
  ("factory_convex", pl(&Occil.FactoryExtra.convexCombination &(ints [1, 2])
    (inr((&p, inr((&r, inl(#())))))) #())),
  ("factory_integral", pl(&Occil.FactoryExtra.integralMixture
    (fun u, &Occil.uniformInt #3) (fun x u, &Occil.rationalCoin x #3) #())),
  ("factory_envelope", pl(&Occil.FactoryExtra.envelopeFactory &p
    (fun n heads, if n < #2 then ((#0, #1), (#1, #1)) else
      let a := heads * (heads - #1); let b := n * (n - #1); ((a, b), (a, b))) #())),
  ("factory_approximate_square", pl(&Occil.FactoryExtra.approximateFactory &p #20 #scale
    (fun s estimate, estimate * estimate / s) #())),
  ("factory_minimum", pl(&Occil.FactoryExtra.minimumComplement &p #())),
  ("factory_minimum_half", pl(&Occil.FactoryExtra.minimumHalf &p #())),
  ("factory_complement_ratio", pl(&Occil.FactoryExtra.oneMinusOverOnePlus &p #())),
  ("factory_sigmoid", pl(&Occil.FactoryExtra.sigmoidRational #(-2) #3 #())),
  ("factory_sigmoid_scaled", pl(&Occil.FactoryExtra.sigmoidScaled &p #3 #2 #())),
  ("factory_logistic_exp", pl(&Occil.FactoryExtra.logisticExp #3 #2 #())),
  ("factory_tanh", pl(&Occil.FactoryExtra.tanhRational #2 #3 #())),
  ("factory_tanh_scaled", pl(&Occil.FactoryExtra.tanhScaled &p #3 #2 #())),
  ("factory_tanh_shifted", pl(&Occil.FactoryExtra.tanhHalfShifted &p #1 #2 #())),
  ("factory_twist", pl(&Occil.FactoryExtra.exponentialTwist &p #2 #3 #())),
  ("factory_exp_ratio", pl(&Occil.FactoryExtra.exponentialRatio #2 #3 #1 #2 #())),
  ("factory_inverse_quadratic", pl(&Occil.FactoryExtra.inverseQuadratic &p #1 #())),
  ("factory_reciprocal_power", pl(&Occil.FactoryExtra.reciprocalAffinePower &p #2 #1 #1 #1 #2 #())),
  ("factory_offset_race", pl(&Occil.FactoryExtra.offsetRace &p &r #1 #1 #1 #2 #())),
  ("factory_exp_integral0", pl(&Occil.FactoryExtra.expIntegral &p #0 #())),
  ("factory_exp_integral1", pl(&Occil.FactoryExtra.expIntegral &p #1 #())),
  ("factory_log_affine", pl(&Occil.FactoryExtra.logOverAffine &p #2 #1 #())),
  ("factory_sinc", pl(&Occil.FactoryExtra.sincScaled &p #2 #1 #())),
  ("factory_cos_sqrt", pl(&Occil.FactoryExtra.cosineSqrt &p #())),
  ("factory_exp_polynomial", pl(&Occil.FactoryExtra.expMinusPolynomial &p
    &(fractions [(1, 5), (1, 2), (1, 3)]) #())),
  ("factory_exp_shift_power", pl(&Occil.FactoryExtra.expMinusShiftPower &p #1 #2 #())),
  ("factory_exp_div_three", pl(&Occil.FactoryExtra.expDivThree &p #())),
  ("factory_exp_nested", pl(&Occil.FactoryExtra.expMinusExp &p #0 #())),
  ("factory_polynomial", pl(&Occil.FactoryExtra.polynomial &p &(fractions [(1, 5), (1, 2), (-1, 5)]) #())),
  ("factory_rational_function", pl(&Occil.FactoryExtra.rationalFunction &p
    &(fractions [(1, 5), (1, 2)]) &(fractions [(2, 5), (-1, 5)]) #())),
  ("factory_piecewise0", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #0 #())),
  ("factory_piecewise1", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #1 #())),
  ("factory_piecewise2", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #2 #())),
  ("factory_piecewise3", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #3 #())),
  ("factory_piecewise4", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #4 #())),
  ("factory_piecewise5", pl(&Occil.FactoryExtra.threePointPiecewise &p &r &h #5 #())),
  ("factory_arctan_pi", pl(&Occil.FactoryExtra.arctanOverPi &p #())),
  ("factory_sinc_sqrt", pl(&Occil.FactoryExtra.sincSqrtScaled &p #2 #1 #())),
  ("factory_p_log_inverse", pl(&Occil.FactoryExtra.pLogInverse &p #())),
  ("factory_complement_log_inverse", pl(&Occil.FactoryExtra.complementLogInverse &p #())),
  ("factory_p_over_log_inverse", pl(&Occil.FactoryExtra.pOverLogInverseComplement &p #())),
  ("factory_complement_over_log_inverse", pl(&Occil.FactoryExtra.complementOverLogInverse &p #())),
  ("factory_polylogarithm", pl(&Occil.FactoryExtra.polylogarithm &p #2 #())),
  ("factory_complement_cos", pl(&Occil.FactoryExtra.complementOverCosine &p #())),
  ("factory_complement_tan", pl(&Occil.FactoryExtra.complementTimesTangent &p #())),
  ("factory_arcsine_sqrt", pl(&Occil.FactoryExtra.arcsinePlusSqrtMinusOne &p #())),
  ("factory_arcsine_half", pl(&Occil.FactoryExtra.arcsineHalf &p #())),
  ("factory_exp_square_complement", pl(&Occil.FactoryExtra.expSquareTimesComplement &p #())),
  ("factory_reciprocal_exp_affine", pl(&Occil.FactoryExtra.reciprocalExpAffine #2 #1 #1 #2 #())),
  ("factory_one_plus_half", pl(&Occil.FactoryExtra.onePlusHalf &p #())),
  ("factory_complement_half", pl(&Occil.FactoryExtra.complementHalf &p #())),
  ("factory_complement_log_one_plus", pl(&Occil.FactoryExtra.complementLogOnePlus &p #())),
  ("factory_odds_product", pl(&Occil.FactoryExtra.oddsProduct &p &r #())),
  ("factory_sigmoid_derivative", pl(&Occil.FactoryExtra.sigmoidDerivative #2 #3 #())),
  ("factory_binary_exp", pl(&Occil.FactoryExtra.binaryExponential &p #2 #1 #())),
  ("factory_binary_exp_rational", pl(&Occil.FactoryExtra.binaryExponentialRational &p #3 #2 #())),
  ("factory_p_over_tangent", pl(&Occil.FactoryExtra.pOverTangent &h #1 #20 #())),
  ("factory_envelope_degrees", pl(&Occil.FactoryExtra.envelopeFactoryDegrees &p
    (fun n heads, if n < #2 then ((#0, #1), (#1, #1)) else
      let a := heads * (heads - #1); let b := n * (n - #1); ((a, b), (a, b)))
    (fun n, if n = #0 then #1 else #3 * n) #())),
  ("constant_digits", pl(&Occil.Constants.fromDigits #10 (fun k, #3) #())),
  ("constant_approx_digits", pl(&Occil.Constants.fromApproximateDigits #2
    (fun k, &Occil.FactoryExtra.intPower #2 k / #3) #())),
  ("constant_bounds", pl(&Occil.Constants.fromBounds (fun n, (#2, (#2, #5))) #())),
  ("constant_positive_series", pl(&Occil.Constants.fromPositiveSeries
    (fun n, let power := &Occil.FactoryExtra.intPower #4 (n + #1);
      (#1, (power, (#1, #3 * power)))) #())),
  ("constant_continued_fraction", pl(&Occil.Constants.continuedFraction
    (fun i, if i = #3 then (#2, #true) else (#1, #false)) #())),
  ("constant_generalized_fraction", pl(&Occil.Constants.generalizedContinuedFraction
    (fun i, if i = #2 then (#2, (#3, #true)) else (#1, (#2, #false))) #1)),
  ("constant_continued_log", pl(&Occil.Constants.continuedLogarithm
    (fun i, if i = #2 then (#1, #true) else (#0, #false)) #1)),
  ("constant_golden", pl(&Occil.Constants.inverseGoldenRatio #())),
  ("constant_sqrt2minus1", pl(&Occil.Constants.sqrtTwoMinusOne #())),
  ("constant_inverse_sqrt2", pl(&Occil.Constants.inverseSqrtTwo #())),
  ("constant_pi_quarter", pl(&Occil.Constants.piQuarter #())),
  ("constant_pi_twelfth", pl(&Occil.Constants.piTwelfth #())),
  ("constant_pi_quarter_minus_half", pl(&Occil.Constants.piQuarterMinusHalf #())),
  ("constant_pi_minus3_over4", pl(&Occil.Constants.piMinusThreeOverFour #())),
  ("constant_pi_minus3", pl(&Occil.Constants.piMinusThree #())),
  ("constant_inverse_pi", pl(&Occil.Constants.inversePi #())),
  ("constant_four_over_three_pi", pl(&Occil.Constants.fourOverThreePi #())),
  ("constant_e_minus2", pl(&Occil.Constants.eMinusTwo #())),
  ("constant_e_third", pl(&Occil.Constants.eDivThree #())),
  ("constant_e_quarter", pl(&Occil.Constants.eQuarter #())),
  ("constant_three_minus_e", pl(&Occil.Constants.threeMinusE #())),
  ("constant_inverse_e_plus", pl(&Occil.Constants.inverseEPlus #2 #())),
  ("constant_tanh_half", pl(&Occil.Constants.tanhHalf #())),
  ("constant_zeta3", pl(&Occil.Constants.threeZetaThreeOverFour #())),
  ("constant_zeta_related", pl(&Occil.Constants.zetaRelated #3 #())),
  ("constant_euler", pl(&Occil.Constants.eulerMascheroni #())),
  ("constant_log_rational", pl(&Occil.Constants.logOnePlusRational #2 #3 #())),
  ("constant_logpi_overpi", pl(&Occil.Constants.logPiOverPi #())),
  ("constant_integer_power", pl(&Occil.Constants.rationalIntegerPower #2 #3 #4 #())),
  ("constant_exp_product", pl(&Occil.Constants.exponentialRationalProduct #2 #3 #3 #2 #())),
  ("constant_golden_family", pl(&Occil.Constants.goldenFamily #1 #1 #2 #())),
  ("constant_e_overpi", pl(&Occil.Constants.eOverPi #())),
  ("constant_inverse_sqrtpi", pl(&Occil.Constants.inverseSqrtPi #())),
  ("constant_arctan_ratio", pl(&Occil.Constants.arctanRationalOverRatio #2 #3 #())),
  ("constant_erf_ratio", pl(&Occil.Constants.erfRatio #real (0.5 : Float) #())),
  ("constant_gamma_integer", pl(&Occil.Constants.lowerGammaIntegerRatio #2 #real (0.5 : Float) #())),
  ("constant_numerical_power", pl(&Occil.Constants.numericalRationalPower #scale #2 #3 #(q 3 2) #())),
  ("constant_numerical_gamma", pl(&Occil.Constants.numericalLowerGammaRatio #scale #(q 3 2) #(q 1 2) #())),
  ("constant_numerical_euler", pl(&Occil.Constants.numericalEulerReciprocal #scale #())),
  ("constant_numerical_exp_product", pl(&Occil.Constants.numericalExpRationalProduct #scale #2 #3 #3 #2 #())),
  ("constant_numerical_logpi", pl(&Occil.Constants.numericalLogPiOverPi #scale #()))
]

end WideExtras
