import FactoryFixtures
import VectorFixtures
import PointFixtures
import Samplers.Numeric
import Samplers.Numerical
import Samplers.Weighted
import Samplers.WeightedVariants
import Samplers.General
import Samplers.DiscreteExtra
import Samplers.DiscreteExtra.Numerical
import Metrology.ProbLang.Interp.BigStepIO
import Lean.Data.Json.FromToJson

/-! Executable fixtures for the expanded numerical and exact sampler library.
Only syntax and literal inputs are assembled in Lean: every calculation and
random draw is performed by the upstream ProbLang interpreter. -/
open ProbLang Lean

private def scale : Int := 1048576
private def q (n : Int) (d : Int := 1) : Int := scale * n / d
private def app (f : Exp Float) (xs : List Int) : Exp Float :=
  xs.foldl (fun e x => .app e (.lit (.int x))) f
private def draw (f : Exp Float) (xs : List Int) : Exp Float :=
  .app (app f xs) (.lit .unit)

private def ints (xs : List Int) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.int x)) tail)) (.inl (.lit .unit))
private def matrix (xs : List (List Int)) : Exp Float :=
  xs.foldr (fun row tail => .inr (.pair (ints row) tail)) (.inl (.lit .unit))
private def ratios (xs : List (Int × Int)) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair
    (.pair (.lit (.int x.1)) (.lit (.int x.2))) tail)) (.inl (.lit .unit))

private def coreCases : List (String × Exp Float) := [
  ("num_mul", app Occil.Numeric.mul [scale, q (-3) 2, q 7 3]),
  ("num_div", app Occil.Numeric.div [scale, q (-7) 3, q 3 2]),
  ("num_sqrt", app Occil.Numeric.sqrt [scale, q 2]),
  ("num_exp", app Occil.Numeric.exp [scale, q (-3) 2]),
  ("num_log", app Occil.Numeric.log [scale, q 3 2]),
  ("num_pow", app Occil.Numeric.pow [scale, q 3 2, q 7 3]),
  ("num_sin", app Occil.Numeric.sin [scale, q 3 2]),
  ("num_cos", app Occil.Numeric.cos [scale, q (-3) 2]),
  ("num_tan", app Occil.Numeric.tan [scale, q 1 3]),
  ("num_atan", app Occil.Numeric.atan [scale, q (-7) 3]),
  ("num_pi", app Occil.Numeric.pi [scale]),
  ("num_cdf", app Occil.Numeric.normalCDF [scale, q 3 2]),
  ("num_quantile", app Occil.Numeric.normalQuantile [scale, q 9 10]),
  ("numeric_uniform", draw Occil.Numeric.uniform [scale]),
  ("numeric_coin", draw Occil.Numeric.coin [scale, q 2 5]),
  ("uniform_range", draw Occil.Numerical.uniformRange [scale, q (-2), q 3]),
  ("exponential_rate", draw Occil.Numerical.exponential [scale, q 3 2]),
  ("normal_box_muller", draw Occil.Numerical.normalBoxMuller [scale, q 1, q 3 2]),
  ("normal_polar", draw Occil.Numerical.normalPolar [scale, q 1, q 3 2]),
  ("normal", draw Occil.Numerical.normal [scale, q 1, q 3 2]),
  ("normal_ratio", draw Occil.Numerical.normalRatioOfUniforms [scale, q 1, q 3 2]),
  ("normal_inversion", draw Occil.Numerical.normalInversion [scale, q 1, q 3 2]),
  ("normal_clt", draw Occil.Numerical.normalCLT [scale, 0, scale]),
  ("gamma", draw Occil.Numerical.gamma [scale, q 5 2, q 3 2]),
  ("gamma_small", draw Occil.Numerical.gamma [scale, q 3 4, q 3 2]),
  ("beta", draw Occil.Numerical.beta [scale, q 2, q 3]),
  ("beta_small", draw Occil.Numerical.beta [scale, q 3 4, q 5 4]),
  ("lognormal", draw Occil.Numerical.lognormal [scale, 0, q 1 2]),
  ("laplace", draw Occil.Numerical.laplace [scale, q 1, q 2]),
  ("logistic", draw Occil.Numerical.logistic [scale, 0, scale]),
  ("cauchy", draw Occil.Numerical.cauchy [scale, 0, scale]),
  ("cauchy_disk", draw Occil.Numerical.cauchyDisk [scale, 0, scale]),
  ("chi_squared", draw Occil.Numerical.chiSquared [scale, q 3]),
  ("noncentral_chi_squared", draw Occil.Numerical.noncentralChiSquared [scale, q 3, q 2]),
  ("student_t", draw Occil.Numerical.studentT [scale, q 5, 0]),
  ("fisher_f", draw Occil.Numerical.fisherF [scale, q 4, q 8, 0]),
  ("inverse_gamma", draw Occil.Numerical.inverseGamma [scale, q 3, q 2]),
  ("inverse_gaussian", draw Occil.Numerical.inverseGaussian [scale, q 2, q 3]),
  ("weibull", draw Occil.Numerical.weibull [scale, q 3 2, q 2]),
  ("pareto", draw Occil.Numerical.pareto [scale, q 3, q 2]),
  ("rayleigh", draw Occil.Numerical.rayleigh [scale, q 2]),
  ("gumbel", draw Occil.Numerical.gumbel [scale, q 1, q 2]),
  ("gev", draw Occil.Numerical.generalizedExtremeValue [scale, q 1 4, 0, scale]),
  ("frechet", draw Occil.Numerical.frechet [scale, q 3, q 1, q 2]),
  ("triangular", draw Occil.Numerical.triangular [scale, 0, q 1 4, scale]),
  ("triangular_uniforms", draw Occil.Numerical.triangularUniforms [scale, q 1 2]),
  ("kumaraswamy", draw Occil.Numerical.kumaraswamy [scale, q 2, q 3]),
  ("beta_prime", draw Occil.Numerical.betaPrime [scale, q 2, q 3, scale]),
  ("beta_pert", draw Occil.Numerical.betaPERT [scale, 0, q 1 4, scale, q 4]),
  ("noncentral_beta", draw Occil.Numerical.noncentralBeta [scale, q 2, q 3, q 1]),
  ("half_normal", draw Occil.Numerical.halfNormal [scale, q 2]),
  ("chi", draw Occil.Numerical.chi [scale, q 3]),
  ("inverse_chi_squared", draw Occil.Numerical.inverseChiSquared [scale, q 5]),
  ("levy", draw Occil.Numerical.levy [scale, q 1, q 2]),
  ("maxwell", draw Occil.Numerical.maxwell [scale, q 2]),
  ("wigner", draw Occil.Numerical.wignerSemicircle [scale, 0, scale]),
  ("parabolic", draw Occil.Numerical.parabolic [scale]),
  ("arcsine", draw Occil.Numerical.arcsine [scale]),
  ("generalized_normal", draw Occil.Numerical.generalizedNormal [scale, q 2, 0, scale]),
  ("generalized_gamma", draw Occil.Numerical.generalizedGamma [scale, q 2, q 2, 0, scale]),
  ("generalized_inverse_gamma", draw Occil.Numerical.generalizedInverseGamma [scale, q 2, q 2, 0, scale]),
  ("birnbaum_saunders", draw Occil.Numerical.birnbaumSaunders [scale, scale, scale]),
  ("tukey_lambda", draw Occil.Numerical.tukeyLambda [scale, scale]),
  ("generalized_tukey_lambda", draw Occil.Numerical.generalizedTukeyLambda [scale, scale, scale, q 2, q 3, q 1]),
  ("power_law_negative", draw Occil.Numerical.powerLaw [scale,scale,q 2,q (-2)]),
  ("power_law", draw Occil.Numerical.powerLaw [scale, scale, q 2, scale]),
  ("power_distribution", draw Occil.Numerical.powerDistribution [scale, q 2, q 2]),
  ("logarithmic_product", draw Occil.Numerical.logarithmicProduct [scale]),
  ("double_logarithmic", draw Occil.Numerical.doubleLogarithmic [scale]),
  ("bates", draw Occil.Numerical.bates [scale, 3]),
  ("skew_normal", draw Occil.Numerical.skewNormal [scale, q 2, 0, scale]),
  ("generalized_skew_normal", draw Occil.Numerical.generalizedSkewNormal [scale, 0, 0]),
  ("twin_t", draw Occil.Numerical.twinT [scale, q 5]),
  ("moyal", draw Occil.Numerical.moyal [scale, 0, scale]),
  ("power_normal", draw Occil.Numerical.powerNormal [scale, q 2, 0, scale]),
  ("power_lognormal", draw Occil.Numerical.powerLognormal [scale, q 2, 0, scale]),
  ("weighted_bits", app Occil.Weighted.randomBits [4]),
  ("weighted_bitmask", app Occil.Weighted.bitmaskRejection [7]),
  ("weighted_fyky", app Occil.Weighted.fyky [7]),
  ("weighted_modulo", app Occil.Weighted.moduloReduction [5, 3]),
  ("weighted_shift", app Occil.Weighted.multiplyShift [5, 3]),
  ("weighted_recycler", app Occil.Weighted.recycledSamples [3, 3]),
  ("weighted_cumulative", pl(&Occil.Weighted.cumulativeChoice &(ints [1,0,3,6]) #())),
  ("weighted_rational", pl(&Occil.Weighted.rationalChoice &(ratios [(1,2),(1,3),(1,6)]) #())),
  ("weighted_knuth_yao", pl(&Occil.Weighted.knuthYao &(ints [1,0,3,6]) #())),
  ("weighted_fldr", pl(&Occil.Weighted.fastLoadedDiceRoller &(ints [1,0,3,6]) #())),
  ("weighted_han_hoshi", pl(&Occil.Weighted.hanHoshi &(ints [1,0,3,6]) #())),
  ("weighted_rational_uniform", draw Occil.Weighted.uniformRational [7]),
  ("weighted_dyadic", draw Occil.Weighted.uniformDyadic [4]),
  ("weighted_fixed", draw Occil.Weighted.uniformFixed [13]),
  ("weighted_float", draw Occil.Weighted.uniformBinaryFloat [2,3]),
  ("weighted_reservoir", pl(&Occil.Weighted.weightedReservoirOne &(ints [1,0,3,6]) #())),
  ("weighted_splitting", pl(&Occil.Weighted.inclusionSplitting &(ints [1,2,3,4]) #2)),
  ("weighted_systematic", pl(&Occil.Weighted.inclusionSystematic &(ints [1,2,3,4]) #2)),
  ("general_string", pl(&Occil.General.randomString &(ints [0,1,2]) #3)),
  ("general_date", app Occil.General.randomDateTime [-2,3]),
  ("general_discrete_cdf", pl(&Occil.General.discreteCDF &(ints [1,3,6]) #())),
  ("general_inverse_cdf", pl(&Occil.General.inverseCDF #12 (fun x, (x + #1) * #3) #0 #3 #())),
  ("general_pdf", pl(&Occil.General.pdfRejection (fun x, x + #1) #0 #4 #4 #())),
  ("general_piecewise_constant", pl(&Occil.General.piecewiseConstant &(ints [0,2,5]) &(ints [1,3]) #())),
  ("general_piecewise_linear", pl(&Occil.General.piecewiseLinear &(ratios [(0,0),(3,3),(7,0)]) #())),
  ("general_refined_coin", pl(&Occil.General.refinedCoin
    (fun level, let d := &Occil.Weighted.integerPower #2 level; (d / #3, (d + #2) / #3)) #())),
  ("general_incomplete", pl(&Occil.General.incompleteInformation #3
    (fun index level, let d := &Occil.Weighted.integerPower #2 level;
      if index = #2 then (d,d) else (d * (index + #1) / #4, (d * (index + #1) + #3) / #4)) #())),
  ("general_markov", pl(&Occil.General.markovChain &(matrix [[1,3],[2,2]]) #0 #1)),
  ("general_perfect", pl(&Occil.General.perfectFiniteChain &(matrix [[1,3],[2,2]]) #())),
  ("general_metropolis", pl(&Occil.General.metropolis (fun x, x + #1)
    (fun x, &Occil.uniformInt #4) #0 #50)),
  ("general_mh", pl(&Occil.General.metropolisHastings
    (fun x, if x = #0 then #1 else #4)
    (fun x, &Occil.General.markovStep &(matrix [[1,3],[2,2]]) x)
    (fun x y, if x = #0 then if y = #0 then (#1,#4) else (#3,#4) else (#1,#2)) #0 #50)),
  ("general_slice", pl(&Occil.General.sliceSampler (fun x, x + #1) #0 #4 #0 #30)),
  ("general_slice_stepout", pl(&Occil.General.sliceSamplerStepOut
    (fun x, if (x < #0) || (#4 <= x) then #0 else x + #1) #0 #2 #4 #30)),
  ("general_walk_path", pl(&Occil.General.randomWalkPath
    (fun u, if &Occil.fairCoin #() then #1 else #(-1)) #0 #3)),
  ("general_stopped_sum", pl(&Occil.General.stoppedSum (fun u, &Occil.poissonRational #2 #1)
    (fun u, if &Occil.rationalCoin #3 #10 then #1 else #0) #())),
  ("general_stopped_min", pl(&Occil.General.stoppedMinimum (fun u, #3)
    (fun u, &Occil.uniformInt #5) #())),
  ("general_stopped_max", pl(&Occil.General.stoppedMaximum (fun u, #3)
    (fun u, &Occil.uniformInt #5) #())),
  ("general_episodes", pl(&Occil.General.episodes (fun u, #3)
    (fun u, if &Occil.rationalCoin #2 #5 then #1 else #0) #())),
  ("discrete_half_bits", app Occil.DiscreteExtra.binomialHalfBits [10]),
  ("discrete_half_rejection", app Occil.DiscreteExtra.binomialHalfRejection [10]),
  ("discrete_binary", app Occil.DiscreteExtra.binomialBinary [12,2,5]),
  ("discrete_polya", app Occil.DiscreteExtra.polyaRational [3,2,3,5]),
  ("discrete_beta_nb", app Occil.DiscreteExtra.betaNegativeBinomial [2,3,1,2,1]),
  ("discrete_borel", app Occil.DiscreteExtra.borel [1,3]),
  ("discrete_logseries", app Occil.DiscreteExtra.logarithmicSeries [2,5]),
  ("discrete_zt_poisson", app Occil.DiscreteExtra.zeroTruncatedPoisson [2,1]),
  ("discrete_compound", pl(&Occil.DiscreteExtra.compoundPoisson #3 #2 (fun u, #2))),
  ("discrete_skellam", app Occil.DiscreteExtra.skellam [3,1,1,1]),
  ("discrete_polya_aeppli", app Occil.DiscreteExtra.polyaAeppli [3,2,1,2]),
  ("discrete_neyman", app Occil.DiscreteExtra.neymanTypeA [3,2,2,1]),
  ("discrete_wallenius", app Occil.DiscreteExtra.walleniusHypergeometric [4,3,5,2,1]),
  ("discrete_fisher", app Occil.DiscreteExtra.fisherHypergeometric [4,3,5,2,1]),
  ("discrete_symmetric", pl(&Occil.DiscreteExtra.symmetricGeometric (fun u, &Occil.rationalCoin #1 #2) #())),
  ("discrete_laplace", app Occil.DiscreteExtra.discreteLaplace [1,1]),
  ("discrete_log_uniform", app Occil.DiscreteExtra.logUniform [15,2]),
  ("discrete_zipf", app Occil.DiscreteExtra.zipf [5,2,1]),
  ("discrete_zeta", app Occil.DiscreteExtra.zeta [2,1]),
  ("discrete_generalized_geometric", pl(&Occil.DiscreteExtra.generalizedGeometric (fun k, &Occil.rationalCoin #1 #2))),
  ("discrete_sibuya", app Occil.DiscreteExtra.generalizedSibuya [2,1,2,1]),
  ("discrete_himanshu", pl(&Occil.DiscreteExtra.himanshu (fun u, &Occil.rationalCoin #1 #2) #2)),
  ("discrete_nb_numerical", draw Occil.DiscreteExtra.negativeBinomialNumerical [scale,q 3 2,q 3 5]),
  ("discrete_beta_nb_numerical", draw Occil.DiscreteExtra.betaNegativeBinomialNumerical [scale,2,q 3,q 2]),
  ("discrete_bell", draw Occil.DiscreteExtra.bell [scale,q 1 2]),
  ("normal_clt_warped", draw Occil.Numerical.normalCLTWarped [scale,0,scale]),
  ("normal_clt_k", draw Occil.Numerical.normalCLTK [scale,12]),
  ("q_gaussian", draw Occil.Numerical.qGaussian [scale,scale,q 1,q 3 2]),
  ("gamma_small_shape", draw Occil.Numerical.gammaSmallShape [scale,q 3 4,q 3 2]),
  ("power_function", draw Occil.Numerical.powerFunction [scale,q 2,q 2]),
  ("stacy", draw Occil.Numerical.stacy [scale,q 2,q 2,q 2]),
  ("amoroso", draw Occil.Numerical.amoroso [scale,q 2,q 2,q 1,q 2]),
  ("pearson_vi", draw Occil.Numerical.pearsonVI [scale,q 2,q 3]),
  ("singh_maddala", draw Occil.Numerical.singhMaddala [scale,q 3,q 2]),
  ("dagum", draw Occil.Numerical.dagum [scale,q 3,q 2]),
  ("log_logistic", draw Occil.Numerical.logLogistic [scale,q 2]),
  ("minimum_uniform", draw Occil.Numerical.minUniform [scale,3]),
  ("maximum_uniform", draw Occil.Numerical.maxUniform [scale,3]),
  ("hypoexponential", pl(&Occil.Numerical.hypoexponential #scale &(ints [q 1,q 2]) #())),
  ("hyperexponential", pl(&Occil.Numerical.hyperexponential #scale &(ints [q 1,q 2]) &(ints [1,3]) #())),
  ("numerical_piecewise_linear", pl(&Occil.Numerical.piecewiseLinear #scale &(ints [0,q 1 4,scale]) &(ints [0,scale,0]) #())),
  ("numerical_piecewise_constant", pl(&Occil.Numerical.piecewiseConstant #scale &(ints [0,q 1 4,scale]) &(ints [scale,q 3]) #())),
  ("sine_power", draw Occil.Numerical.sinePower [scale,scale]),
  ("skew_normal_extremes", draw Occil.Numerical.skewNormalExtremes [scale,q 1 2,0,scale]),
  ("skew_normal_conditional", draw Occil.Numerical.generalizedSkewNormalConditional [scale,q 2,0]),
  ("weighted_lemire", app Occil.WeightedVariants.lemireUniform [7,4]),
  ("weighted_sequential", pl(&Occil.WeightedVariants.sequentialCoins &(ints [1,0,3,6]) #())),
  ("weighted_optimal", pl(&Occil.WeightedVariants.optimalChoice &(ints [1,0,3,6]) #())),
  ("weighted_sorted", pl(&Occil.WeightedVariants.sortedChoice &(ints [0,1,3,6]) #())),
  ("weighted_succinct", pl(&Occil.WeightedVariants.succinctChoice &(ints [1,0,3,6]) #())),
  ("weighted_vose", pl(&Occil.WeightedVariants.voseSamples &(ints [1,0,3,6]) #3)),
  ("weighted_two_level", pl(&Occil.WeightedVariants.twoLevelChoice &(ints [1,0,3,6]) #2 #())),
  ("weighted_flat", pl(&Occil.WeightedVariants.flatChoice &(ints [1,0,3,6]) #())),
  ("general_inverse_quantile", pl(&Occil.General.inverseQuantile #12 (fun s p, p) #())),
  ("general_shape", pl(&Occil.General.shapeRejection (fun u, &Occil.uniformInt #10) (fun x, x % #2 = #0) #())),
  ("general_markov_trajectory", pl(&Occil.General.markovTrajectory &(matrix [[1,3],[2,2]]) #0 #2)),
  ("general_gibbs", pl(&Occil.General.gibbsSweep #2
    (fun index state, if index = #0 then #2 * (state / #2) + (if &Occil.rationalCoin #1 #4 then #1 else #0)
      else state % #2 + (if &Occil.rationalCoin #3 #4 then #2 else #0)) #0)),
  ("general_random_scan_gibbs", pl(&Occil.General.randomScanGibbs #2
    (fun index state, if index = #0 then #2 * (state / #2) + (if &Occil.rationalCoin #1 #4 then #1 else #0)
      else state % #2 + (if &Occil.rationalCoin #3 #4 then #2 else #0)) #0 #30)),
  ("general_permutation", pl(&Occil.General.permutationTest &(ints [0,1,2,3]) &Occil.sumInts #8)),
  ("discrete_beta_binomial", app Occil.DiscreteExtra.betaBinomial [8,3,1,2,1]),
  ("discrete_negative_hypergeometric", app Occil.DiscreteExtra.negativeHypergeometric [2,4,6]),
  ("weighted_division", app Occil.WeightedVariants.divisionRejection [7,4]),
  ("weighted_debiased", app Occil.WeightedVariants.debiasedModulo [7,4]),
  ("weighted_oneill", app Occil.WeightedVariants.oneillUniform [7,4]),
  ("weighted_floating_multiply", app Occil.WeightedVariants.floatingMultiply [5,4,4]),
  ("weighted_fenwick", pl(let table := &Occil.WeightedVariants.newFenwick &(ints [1,0,3,6]);
    &Occil.WeightedVariants.fenwickSet table #0 #4;
    &Occil.WeightedVariants.fenwickSet table #3 #0;
    &Occil.WeightedVariants.fenwickDraw table #())),
  ("discrete_waring", app Occil.DiscreteExtra.waringYule [3,1,2,1]),
  ("discrete_yule_simon", app Occil.DiscreteExtra.yuleSimon [3,1]),
  ("discrete_inverse_polya", app Occil.DiscreteExtra.inversePolya [2,3,2,1]),
  ("discrete_cub", app Occil.DiscreteExtra.cub [5,2,5,1,3]),
  ("discrete_multipoisson", pl(&Occil.DiscreteExtra.multivariatePoisson #2 #1 &(ratios [(1,1),(3,1)]))),
  ("discrete_negative_multinomial", pl(&Occil.DiscreteExtra.negativeMultinomial #2 #2 &(ints [1,3]))),
  ("discrete_multivariate_hypergeometric", pl(&Occil.DiscreteExtra.multivariateHypergeometric #4 &(ints [2,3,5]))),
  ("discrete_wallenius_multivariate", pl(&Occil.DiscreteExtra.walleniusMultivariate #4 &(ints [2,3,5]) &(ints [1,2,1]))),
  ("discrete_fisher_multivariate", pl(&Occil.DiscreteExtra.fisherMultivariate #4 &(ints [2,3,5]) &(ints [1,2,1]))),
  ("discrete_bell_touchard", draw Occil.DiscreteExtra.bellTouchard [scale,q 1 2,q 3 2]),
  ("discrete_pareto", draw Occil.DiscreteExtra.discretePareto [scale,q 1 5,q 2 5]),
  ("invalid_numeric_log", app Occil.Numeric.log [scale, 0]),
  ("invalid_numeric_sqrt", app Occil.Numeric.sqrt [scale, -1]),
  ("invalid_numeric_div", app Occil.Numeric.div [scale, scale, 0]),
  ("invalid_gamma", draw Occil.Numerical.gamma [scale, 0, scale])
]

private def cases : List (String × Exp Float) := coreCases ++ WideExtras.factoryCases ++ WideExtras.vectorCases ++ WideExtras.pointCases

private partial def encodeValue : Exp Float → Except String Json
  | .lit (.int z) => .ok (toJson z)
  | .lit (.bool b) => .ok (toJson b)
  | .lit (.real r) => if r.isFinite then .ok (.str s!"f64:{r.toBits.toNat}")
      else .error "non-finite real returned"
  | .lit .unit => .ok Json.null
  | .pair x y => do return .arr #[← encodeValue x, ← encodeValue y]
  | .inl (.lit .unit) => .ok (.arr #[])
  | .inr (.pair x xs) => do
      let h ← encodeValue x
      let .arr tail ← encodeValue xs | .error "malformed list tail"
      return .arr (#[h] ++ tail)
  | _ => .error "unexpected output shape"

def main (args : List String) : IO Unit := do
  let stdout ← IO.getStdout
  if args == ["--list"] then
    stdout.putStrLn (toJson (cases.map Prod.fst)).compress
    return
  let [name, countStr, seedStr, engine] := args
    | throw (IO.userError "usage: wide-samples CASE COUNT SEED env|subst")
  let some count := countStr.toNat? | throw (IO.userError "invalid count")
  let some seed := seedStr.toNat? | throw (IO.userError "invalid seed")
  let some (_, term) := cases.find? (fun c => c.1 == name)
    | throw (IO.userError s!"unknown case: {name}")
  unless engine == "env" || engine == "subst" do throw (IO.userError "unknown engine")
  IO.setRandSeed seed
  let mut values : Array Json := #[]
  for _ in [0:count] do
    let value : Exp Float ← if engine == "env" then Interp.eval term else
      (fun cfg => cfg.expr) <$> Interp.runSubst ⟨term, default⟩
    match encodeValue value with
    | .ok j => values := values.push j
    | .error e => throw (IO.userError e)
  stdout.putStrLn (Json.arr values).compress
