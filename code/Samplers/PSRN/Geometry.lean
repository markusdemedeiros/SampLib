import Samplers.PSRN.BetaGamma
import Samplers.PSRN.Gaussian

/-!
# Geometric and vector lazy samplers

Coordinates remain lazy interval oracles. Shared normalizers and radii
are retained, so the coordinates preserve their intended dependence.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

/-- Squared Euclidean norm of a list of lazy coordinates. -/
@[pl_fold] def normSquared : Exp rT := pl%
  rec norm coordinates := case! coordinates
    | inl(u) => &rational #0 #1
    | inr(p) => &add (&multiply (fst(p)) (fst(p))) (norm (snd(p)))

@[pl_fold] def divideCoordinates : Exp rT := pl%
  rec scale coordinates denominator := case! coordinates
    | inl(u) => inl(#())
    | inr(p) => inr((&divide (fst(p)) denominator, scale (snd(p)) denominator))

@[pl_fold] def multiplyCoordinates : Exp rT := pl%
  rec scale coordinates factor := case! coordinates
    | inl(u) => inl(#())
    | inr(p) => inr((&multiply (fst(p)) factor, scale (snd(p)) factor))

/-- Uniform surface measure on the unit sphere in the requested dimension. -/
@[pl_fold] def newSphere : Exp rT := pl%
  fun dimensions u,
    if dimensions <= #0 then fail else
    if dimensions = #1 then
      inr((&rational (if &fairCoin #() then #1 else #(-1)) #1, inl(#())))
    else
      let vector := &repeatSample &newGaussian dimensions;
      let norm := &root (&normSquared vector) #2;
      &divideCoordinates vector norm

/-- Uniform volume measure on a unit ball. The radial CDF is r^dimensions. -/
@[pl_fold] def newBall : Exp rT := pl%
  fun dimensions u,
    if dimensions <= #0 then fail else
      let direction := &newSphere dimensions #();
      let radius := &newPowerUniform #1 dimensions #();
      &multiplyCoordinates direction radius

/-- Uniform shell with positive rational outer radius and nonnegative inner
radius. Radii are given as integer fractions. -/
@[pl_fold] def newShell : Exp rT := pl%
  fun dimensions innerNumerator innerDenominator outerNumerator outerDenominator u,
    if (dimensions <= #0) || (innerNumerator < #0) || (innerDenominator <= #0) ||
      (outerNumerator <= #0) || (outerDenominator <= #0) ||
      (outerNumerator * innerDenominator <= innerNumerator * outerDenominator) then fail else
        let inner := &rational innerNumerator innerDenominator;
        let outer := &rational outerNumerator outerDenominator;
        let lo := &integerPowerReal inner dimensions;
        let hi := &integerPowerReal outer dimensions;
        let radius := &root (&add lo (&multiply (&newUniform #()) (&subtract hi lo))) dimensions;
        &multiplyCoordinates (&newSphere dimensions #()) radius

/-- Dirichlet with positive rational shapes, represented as a list of lazy
coordinates summing to one. Shapes are (numerator,denominator) pairs. -/
@[pl_fold] def newDirichlet : Exp rT := pl%
  fun shapes u,
    let valid := (rec check xs := case! xs
      | inl(v) => #true
      | inr(p) =>
        let shape := fst(p);
        if ((fst(shape)) <= #0) || ((snd(shape)) <= #0) then #false else check (snd(p)));
    let build := (rec draw xs := case! xs
      | inl(v) => inl(#())
      | inr(p) =>
        let shape := fst(p);
        let x := &newGamma (fst(shape)) (snd(shape)) #1 #1 #();
        inr((x, draw (snd(p)))));
    let sum := (rec total xs := case! xs
      | inl(v) => &rational #0 #1
      | inr(p) => &add (fst(p)) (total (snd(p))));
    if ~ (valid shapes) then fail else
    if &length shapes <= #0 then fail else
    if &length shapes = #1 then inr((&rational #1 #1, inl(#()))) else
      let coordinates := build shapes;
      &divideCoordinates coordinates (sum coordinates)

/-- Uniform positive components summing to one, via independent exponentials. -/
@[pl_fold] def newSimplex : Exp rT := pl%
  fun components u,
    if components <= #0 then fail else
    if components = #1 then inr((&rational #1 #1, inl(#()))) else
      let coordinates := &repeatSample (fun u, &newExponential #1 #1 #()) components;
      let sum := (rec total xs := case! xs
        | inl(v) => &rational #0 #1
        | inr(p) => &add (fst(p)) (total (snd(p))));
      &divideCoordinates coordinates (sum coordinates)

end Occil.PSRN
