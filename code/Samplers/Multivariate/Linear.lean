import Samplers.Numeric
import Samplers.Numerical
import Samplers.Combinatorial.Basic

/-! Fixed-point vector and covariance routines. Every real value is an integer
scaled by the positive first argument `scale`. Lists use the shared nil/cons encoding.
These numerical algorithms round at each multiplication/division. -/
namespace Occil.Multivariate
open ProbLang
variable {rT : Type _}

@[pl_fold] def map : Exp rT := pl%
  rec apply f xs := case! xs
    | inl(u) => inl(#())
    | inr(p) => inr((f (fst(p)), apply f (snd(p))))

@[pl_fold] def zeros : Exp rT := pl%
  rec build n := if n < #0 then fail else if n = #0 then inl(#()) else
    inr((#0, build (n - #1)))

@[pl_fold] def constants : Exp rT := pl%
  rec build n x := if n < #0 then fail else if n = #0 then inl(#()) else
    inr((x, build (n - #1) x))

@[pl_fold] def add : Exp rT := pl%
  rec combine xs ys := case! xs
    | inl(u) => case! ys | inl(v) => inl(#()) | inr(q) => fail
    | inr(p) => case! ys | inl(v) => fail | inr(q) =>
      inr(((fst(p)) + (fst(q)), combine (snd(p)) (snd(q))))

@[pl_fold] def scaleVector : Exp rT := pl%
  fun scale factor xs, &map (fun x, &Numeric.mul scale factor x) xs

@[pl_fold] def dot : Exp rT := pl%
  rec product scale xs ys := case! xs
    | inl(u) => case! ys | inl(v) => #0 | inr(q) => fail
    | inr(p) => case! ys | inl(v) => fail | inr(q) =>
      &Numeric.mul scale (fst(p)) (fst(q)) + product scale (snd(p)) (snd(q))

/-- Sum of raw integer coordinate squares, without fixed-point truncation. -/
@[pl_fold] def integerSquares : Exp rT := pl%
  rec sum xs := case! xs | inl(u) => #0 | inr(p) =>
    (fst(p)) * (fst(p)) + sum (snd(p))

@[pl_fold] def squaredNorm : Exp rT := pl%
  fun scale xs, if scale <= #0 then fail else &integerSquares xs / scale

/-- Euclidean norm in the coordinate grid, delaying rounding until after sqrt. -/
@[pl_fold] def norm : Exp rT := pl%
  fun scale xs, if scale <= #0 then fail else &Numeric.sqrt #1 (&integerSquares xs)

@[pl_fold] def matrixVector : Exp rT := pl%
  fun scale matrix vector, &map (fun row, &dot scale row vector) matrix

/-- Lower-triangular Cholesky factor. The matrix must be symmetric positive
 definite, square and resolvable at the requested fixed-point scale. -/
@[pl_fold] def cholesky : Exp rT := pl%
  fun scale matrix,
    let n := &Occil.length matrix;
    if (scale <= #0) || (n <= #0) then fail else
      let shape := (rec check rows := case! rows
        | inl(u) => #true
        | inr(p) => if &Occil.length (fst(p)) = n then check (snd(p)) else #false);
      if shape matrix then
        let result := allocN(n * n, #0);
        let rows := (rec row i := if i = n then #() else
          let columns := (rec col j := if i < j then #() else
            let cross := (rec sum k acc := if k = j then acc else
              let a := !(result +ₗ (i * n + k));
              let b := !(result +ₗ (j * n + k));
              sum (k + #1) (acc + &Numeric.mul scale a b));
            let residual := &Occil.getAt (&Occil.getAt matrix i) j - cross #0 #0;
            let value := (if i = j then
              if residual <= #0 then fail else &Numeric.sqrt scale residual
              else &Numeric.div scale residual (!(result +ₗ (j * n + j))));
            (result +ₗ (i * n + j)) ← value;
            col (j + #1));
          columns #0;
          row (i + #1));
        rows #0;
        let readRows := (rec read i := if i = n then inl(#()) else
          inr((&Occil.readArray result (i * n) ((i + #1) * n), read (i + #1))));
        readRows #0
      else fail

@[pl_fold] def standardNormals : Exp rT := pl%
  fun scale n, &Occil.repeatSample (fun u, &Numerical.normal scale #0 scale #()) n

/-- Transform independent coordinates by mu + chol(covariance)*coordinates. -/
@[pl_fold] def covarianceTransform : Exp rT := pl%
  fun scale means covariance coordinates,
    let n := &Occil.length covariance;
    let center := (if &Occil.length means = #0 then &zeros n else means);
    &add center (&matrixVector scale (&cholesky scale covariance) coordinates)

@[pl_fold] def normal : Exp rT := pl%
  fun scale means covariance u,
    &covarianceTransform scale means covariance
      (&standardNormals scale (&Occil.length covariance))

/-- Bivariate normal with supplied means, standard deviations and correlation. -/
@[pl_fold] def binormal : Exp rT := pl%
  fun scale mu1 mu2 sigma1 sigma2 rho u,
    if ((&Numeric.abs rho) <= scale) && (#0 < sigma1) && (#0 < sigma2) then
      let x := &Numerical.normal scale #0 scale #();
      let z := &Numerical.normal scale #0 scale #();
      let remaining := &Numeric.sqrt scale (scale - &Numeric.mul scale rho rho);
      let y := &Numeric.mul scale rho x + &Numeric.mul scale remaining z;
      (mu1 + &Numeric.mul scale sigma1 x, mu2 + &Numeric.mul scale sigma2 y)
    else fail

/-- Rounding-preserving normalization: the last coordinate receives the residual. -/
@[pl_fold] def normalize : Exp rT := pl%
  fun scale values,
    let total := &Occil.sumInts values;
    if total <= #0 then fail else
      let loop := (rec divide xs remaining := case! xs
        | inl(u) => inl(#())
        | inr(p) => case! snd(p)
          | inl(v) => inr((remaining, inl(#())))
          | inr(q) =>
            let value := &Numeric.div scale (fst(p)) total;
            inr((value, divide (snd(p)) (remaining - value))));
      loop values scale

/-- Gamma-normalization Dirichlet sampler; shape parameters are fixed-point.
Its coordinates sum to scale exactly after final-coordinate rounding correction. -/
@[pl_fold] def dirichlet : Exp rT := pl%
  rec draw scale shapes u :=
    if &Occil.length shapes <= #0 then fail else
      let values := &map (fun shape, &Numerical.gamma scale shape scale #()) shapes;
      if &Occil.sumInts values <= #0 then draw scale shapes #() else &normalize scale values

@[pl_fold] def uniformPartition : Exp rT := pl%
  fun scale count total u,
    if (count <= #0) || (total <= #0) then fail else
      let fractions := &dirichlet scale (&constants count scale) #();
      let allocate := (rec divide xs remaining := case! xs | inl(v) => inl(#()) | inr(p) =>
        case! snd(p) | inl(v) => inr((remaining, inl(#()))) | inr(q) =>
          let amount := &Numeric.mul scale total (fst(p));
          inr((amount, divide (snd(p)) (remaining - amount))));
      allocate fractions total

@[pl_fold] def logNormal : Exp rT := pl%
  fun scale means covariance u, &map (fun x, &Numeric.exp scale x)
    (&normal scale means covariance #())

/-- Normal mean mixture with an independent nonnegative mixing sampler. -/
@[pl_fold] def meanMixture : Exp rT := pl%
  fun scale theta perturbation covariance mixer u,
    let v := mixer #();
    &normal scale (&add theta (&scaleVector scale v perturbation)) covariance #()

/-- Normal mean/variance mixture, using one shared independent mixing variate. -/
@[pl_fold] def meanVarianceMixture : Exp rT := pl%
  fun scale means drift covariance mixer u,
    let v := mixer #();
    if v < #0 then fail else
      &add means (&add (&scaleVector scale v drift)
        (&scaleVector scale (&Numeric.sqrt scale v)
          (&normal scale (inl(#())) covariance #())))

end Occil.Multivariate
