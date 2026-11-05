import Samplers.General
import Metrology.ProbLang.Interp.BigStepIO

/-! Point-set and supplied-model fixtures. All generation occurs in ProbLang;
Lean only constructs input literals and statically supplied data. -/
namespace WideExtras
open ProbLang

private def scale : Int := 1048576
private def q (n : Int) (d : Int := 1) : Int := scale * n / d
private def intLit (n : Int) : Exp Float := .lit (.int n)
private def list (xs : List (Exp Float)) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair x tail)) (.inl (.lit .unit))
private def ints (xs : List Int) : Exp Float := list (xs.map intLit)
private def matrix (xs : List (List Int)) : Exp Float := list (xs.map ints)
private def pairs (xs : List (Int × Int)) : Exp Float :=
  list (xs.map fun x => .pair (intLit x.1) (intLit x.2))
private def applyArgs (f : Exp Float) (xs : List (Exp Float)) : Exp Float := xs.foldl Exp.app f
private def value (f : Exp Float) (xs : List Int) : Exp Float := applyArgs f (xs.map intLit)
private def sample (f : Exp Float) (xs : List (Exp Float)) : Exp Float :=
  .app (applyArgs f xs) (.lit .unit)
private def draw (f : Exp Float) (xs : List Int) : Exp Float := sample f (xs.map intLit)

/-- Names have separate analytic/structural checks in point_oracles.py. -/
def pointCases : List (String × Exp Float) := [
  ("point_vdc_rational", value Occil.General.vanDerCorputRational [2,3]),
  ("point_vdc_prefix", pl(&Occil.General.map
    (fun i, &Occil.General.vanDerCorput #scale #2 i) (&Occil.intRange #0 #8))),
  ("point_halton_prefix", pl(&Occil.General.map
    (fun i, &Occil.General.halton #scale &(ints [2,3]) i) (&Occil.intRange #0 #8))),
  ("point_scrambled", applyArgs Occil.General.scrambledRadicalInverse
    [intLit scale,intLit 2,intLit 0,matrix [[1,0],[1,0],[1,0]]]),
  ("point_shift", applyArgs Occil.General.shiftPoint
    [intLit scale,ints [q 1 4,q 3 4],ints [q 1 2,q 1 2]]),
  ("point_baker", pl(&Occil.General.map
    (fun x, &Occil.General.bakersMap #scale x) &(ints [0,q 1 4,q 1 2,q 3 4,scale]))),
  ("point_roberts", value Occil.General.robertsPoint [scale,2,1]),
  ("point_sobol_prefix", pl(&Occil.General.map
    (fun i, &Occil.General.sobol2 #scale #8 i) (&Occil.intRange #0 #8))),
  ("point_lattice", value Occil.General.latticePoint [scale,2,1]),
  ("point_lfsr_grid8", value Occil.General.lfsrPoint [8,3,3,7,1]),
  ("point_stratified", draw Occil.General.stratified1D [scale,4]),
  ("point_latin1", draw Occil.General.latinHypercube1D [scale,4]),
  ("point_latin3", draw Occil.General.latinHypercube [scale,4,3]),
  ("point_stratified_box", draw Occil.General.stratifiedBox [scale,2,2,2]),
  ("point_best_candidate", draw Occil.General.bestCandidate [scale,2,4,6]),
  ("point_farthest", sample Occil.General.farthestPoints [matrix [[0],[2],[5],[9]],intLit 4]),
  ("point_poisson_disk_grid32", draw Occil.General.poissonDiskRejection [32,2,5,8,300]),
  ("model_bootstrap", sample Occil.General.bootstrap [ints [0,1,2],intLit 2]),
  ("model_permutations", sample Occil.General.permutationSamples [ints [0,1,2],intLit 2]),
  ("model_grouped_permutation", sample Occil.General.groupedPermutation
    [ints [0,1,2,3,4,5],ints [2,1,3]]),
  ("model_histogram_grid", sample Occil.General.histogram [ints [0,2,5],ints [1,3]]),
  ("model_kde", pl(&Occil.General.kernelDensity &(ints [q (-2),q 2])
    (fun u, &Occil.rndIntRange #(q (-1)) #scale) #())),
  ("model_kde_vector", pl(&Occil.General.kernelDensityVector
    &(matrix [[q (-1),q (-1)],[scale,scale]])
    (fun u, &Occil.rndIntRange #(q (-1) 4) #(q 1 4)) #())),
  ("model_gaussian_kde", sample Occil.General.gaussianKernelDensity
    [intLit scale,ints [0],intLit scale]),
  ("model_gaussian_mixture", sample Occil.General.gaussianMixture
    [intLit scale,ints [1,3],pairs [(q (-1),scale),(q 2,q 1 2)]]),
  ("model_regression_zero_error", sample Occil.General.linearRegression
    [intLit scale,ints [q 2,q (-1)],intLit (q 1 2),intLit 0,ints [q 3,q 4]]),
  ("model_regression", sample Occil.General.linearRegression
    [intLit scale,ints [q 2,q (-1)],intLit (q 1 2),intLit (q 1 4),ints [q 3,q 4]]),
  ("model_generative", pl(&Occil.General.generativeModel
    (fun u, &Occil.uniformInt #3) (fun x, x * x) #())),
  ("model_classified", sample Occil.General.classifiedModel
    [ints [1,3],list [pl(fun u, #10),pl(fun u, #20)]]),
  ("model_stochastic_bootstrap", sample Occil.General.stochasticInterpolation
    [intLit scale,matrix [[0,0],[scale,0],[0,scale],[scale,scale]],intLit 1]),
  ("model_stochastic_interpolation", sample Occil.General.stochasticInterpolation
    [intLit scale,matrix [[0,0],[scale,0],[0,scale],[scale,scale]],intLit 4])
]
end WideExtras
