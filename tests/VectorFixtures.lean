import Samplers.Multivariate
import Samplers.Specialized
import Samplers.PSRN
import Metrology.ProbLang.Interp.BigStepIO

/-! Numerical vector/rare-distribution and exact lazy-real fixtures.
These construct only object-language inputs; upstream ProbLang interprets every draw. -/
namespace WideExtras
open ProbLang

private def scale : Int := 1048576
private def q (n : Int) (d : Int := 1) : Int := scale * n / d
private def intLit (n : Int) : Exp Float := .lit (.int n)
private def list (xs : List (Exp Float)) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair x tail)) (.inl (.lit .unit))
private def ints (xs : List Int) : Exp Float := list (xs.map intLit)
private def matrix (xs : List (List Int)) : Exp Float := list (xs.map ints)
private def applyArgs (f : Exp Float) (xs : List (Exp Float)) : Exp Float :=
  xs.foldl Exp.app f
private def sample (f : Exp Float) (xs : List (Exp Float)) : Exp Float :=
  .app (applyArgs f xs) (.lit .unit)
private def draw (f : Exp Float) (xs : List Int) : Exp Float := sample f (xs.map intLit)
private def covariance : Exp Float := matrix [[scale, q 1 2], [q 1 2, q 2]]
private def correlation : Exp Float := matrix [[scale, q 1 2], [q 1 2, scale]]
private def triangleVertices : Exp Float := matrix [[0, 0], [scale, 0], [0, scale]]

/-- All names have dedicated independent oracles in vector_oracles.py. -/
def vectorCases : List (String × Exp Float) := [
  ("vector_normal", sample Occil.Multivariate.normal [intLit scale, ints [0,scale], covariance]),
  ("vector_binormal", draw Occil.Multivariate.binormal [scale,0,0,scale,scale,q 1 2]),
  ("vector_binormal_endpoint", draw Occil.Multivariate.binormal [scale,0,0,scale,scale,scale]),
  ("vector_dirichlet", sample Occil.Multivariate.dirichlet [intLit scale, ints [scale,q 2,q 3]]),
  ("vector_partition", draw Occil.Multivariate.uniformPartition [scale,3,q 2]),
  ("vector_sphere", draw Occil.Multivariate.sphere [scale,3,scale,q 2]),
  ("vector_ball", draw Occil.Multivariate.ball [scale,3,scale,q 2]),
  ("vector_shell", draw Occil.Multivariate.shell [scale,3,scale,q 2,q 2]),
  ("vector_box", sample Occil.Multivariate.box [intLit scale, ints [-scale,0], ints [scale,q 2]]),
  ("vector_hypercube", draw Occil.Multivariate.hypercube [scale,3,-scale,scale]),
  ("vector_cone", draw Occil.Multivariate.cone [scale,q 2,scale]),
  ("vector_cylinder", draw Occil.Multivariate.cylinder [scale,q 2,scale]),
  ("vector_circle", draw Occil.Multivariate.circle [scale,scale]),
  ("vector_latlon", draw Occil.Multivariate.latitudeLongitude [scale]),
  ("vector_simplex", sample Occil.Multivariate.simplex [intLit scale,triangleVertices]),
  ("vector_triangle", sample Occil.Multivariate.triangle
    [intLit scale,ints [0,0],ints [scale,0],ints [0,scale]]),
  ("vector_ellipsoid", sample Occil.Multivariate.ellipsoidSurface [intLit scale,ints [scale,q 2]]),
  ("vector_gaussian_copula", sample Occil.Multivariate.gaussianCopula [intLit scale,correlation]),
  ("vector_product_copula", draw Occil.Multivariate.productCopula [scale,2]),
  ("vector_upper_copula", draw Occil.Multivariate.upperBoundCopula [scale,3]),
  ("vector_lower_copula", draw Occil.Multivariate.lowerBoundCopula [scale]),
  ("vector_clayton", draw Occil.Multivariate.claytonCopula [scale,2,scale]),
  ("vector_gumbel_copula", draw Occil.Multivariate.gumbelCopula [scale,2,q 2]),
  ("vector_exchangeable_fgm", sample Occil.Multivariate.exchangeableFGMCopula
    [intLit scale,ints [1,0,1]]),
  ("vector_student_t", sample Occil.Multivariate.studentT
    [intLit scale,intLit (q 5),ints [0,0],correlation]),
  ("vector_correlated_exponential", draw Occil.Multivariate.correlatedExponential
    [scale,q 1 2,scale,q 2]),
  ("vector_phase_type", sample Occil.Multivariate.phaseType
    [intLit scale,ints [scale],matrix [[-scale]]]),
  ("vector_erlang_phase_type", sample Occil.Multivariate.phaseType
    [intLit scale,ints [scale,0],matrix [[-scale,scale],[0,-scale]]]),
  ("vector_reward_phase_type", sample Occil.Multivariate.multivariatePhaseType
    [intLit scale,ints [scale],matrix [[-scale]],matrix [[scale,q 2]]]),
  ("vector_stable_cauchy", draw Occil.Multivariate.stable [scale,scale,0]),
  ("vector_stable_normal", draw Occil.Multivariate.stable [scale,q 2,0]),
  ("vector_linnik", draw Occil.Multivariate.linnik [scale,q 2,scale]),
  ("vector_mittag_leffler", draw Occil.Multivariate.mittagLeffler [scale,scale,scale]),
  ("vector_von_mises_uniform", draw Occil.Multivariate.vonMises [scale,0,0]),
  ("vector_von_mises", draw Occil.Multivariate.vonMises [scale,0,q 2]),
  ("special_lindley", draw Occil.Specialized.lindley [scale,q 2]),
  ("special_garima", draw Occil.Specialized.garima [scale,q 2]),
  ("special_i_garima", draw Occil.Specialized.iGarima [scale,q 2]),
  ("special_weighted_exp_gamma", draw Occil.Specialized.weightedExponentialGamma [scale,q 2]),
  ("special_xgamma", draw Occil.Specialized.xgamma [scale,q 2]),
  ("special_mirra", draw Occil.Specialized.mirra [scale,scale,q 2]),
  ("special_sushila", draw Occil.Specialized.sushila [scale,q 2,q 2]),
  ("special_xlindley", draw Occil.Specialized.xLindley [scale,q 2]),
  ("special_sech", draw Occil.Specialized.hyperbolicSecant [scale]),
  ("special_epanechnikov", draw Occil.Specialized.epanechnikov [scale]),
  ("special_ratio_uniforms", draw Occil.Specialized.ratioUniforms [scale]),
  ("special_reciprocal_uniform", draw Occil.Specialized.reciprocalUniform [scale]),
  ("special_uniform_odds", draw Occil.Specialized.uniformOdds [scale]),
  ("special_arccosine", draw Occil.Specialized.arcCosine [scale]),
  ("special_exp_log_rate", draw Occil.Specialized.exponentialLogRate [scale,q 2]),
  ("special_tulap", draw Occil.Specialized.tulap [scale,0,q 1 2,0]),
  ("special_tulap_trimmed", draw Occil.Specialized.tulap [scale,0,q 1 2,q 1 2]),
  ("special_continuous_bernoulli", draw Occil.Specialized.continuousBernoulli [scale,q 3 4]),
  ("special_lomax", draw Occil.Specialized.lomax [scale,q 3]),
  ("special_topp_leone", draw Occil.Specialized.toppLeone [scale,q 2]),
  ("special_marshall_olkin", draw Occil.Specialized.marshallOlkin [scale,q 1 2]),
  ("special_unit_lindley", draw Occil.Specialized.unitLindley [scale,q 2]),
  ("special_rectellipse", draw Occil.Specialized.rectellipse [scale,scale,q 2,0]),
  ("psrn_uniform", pl(let x := &Occil.PSRN.newUniform #(); &Occil.PSRN.floorScaled x #256)),
  ("psrn_shared_square", pl(let x := &Occil.PSRN.newUniform #();
    &Occil.PSRN.floorScaled (&Occil.PSRN.multiply x x) #256)),
  ("psrn_independent_product", pl(let x := &Occil.PSRN.newUniform #();
    let y := &Occil.PSRN.newUniform #(); &Occil.PSRN.floorScaled (&Occil.PSRN.multiply x y) #256)),
  ("psrn_reread", pl(let x := &Occil.PSRN.newUniform #();
    let a := &Occil.PSRN.floorScaled x #256; (a,&Occil.PSRN.floorScaled x #256))),
  ("psrn_sum", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newUniformSum #2) #256)),
  ("psrn_beta", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newBeta #2 #1 #3 #1 #()) #256)),
  ("psrn_beta_fractional", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newBeta #3 #2 #5 #4 #()) #256)),
  ("psrn_exponential", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newExponential #2 #1 #()) #256)),
  ("psrn_gamma", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newGammaInteger #2 #2 #1) #256)),
  ("psrn_epanechnikov", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newEpanechnikov #()) #256)),
  ("psrn_cauchy", pl(&Occil.PSRN.floorScaled (&Occil.PSRN.newCauchy #()) #256)),
  ("psrn_rational_arithmetic", pl(let x := &Occil.PSRN.rational #1 #3;
    let y := &Occil.PSRN.rational #2 #5;
    &Occil.PSRN.floorScaled (&Occil.PSRN.add x y) #256)),
  ("psrn_less_rational", pl(&Occil.PSRN.less (&Occil.PSRN.rational #1 #3) (&Occil.PSRN.rational #2 #5)))
]
end WideExtras
