import Samplers.Multivariate.Linear

/-! Numerical geometric samplers from randomfunc.html. Coordinates, lengths,
angles and finite p parameters are fixed-point integers at the supplied scale.
The sentinel p=0 denotes the infinity norm. -/
namespace Occil.Multivariate
open ProbLang
variable {rT : Type _}

@[pl_fold] def uniformRange : Exp rT := pl%
  fun scale lo hi u,
    if hi < lo then fail else lo + &Numeric.mul scale (hi - lo) (&Numeric.uniform scale #())

@[pl_fold] def pNorm : Exp rT := pl%
  fun scale values p,
    if p < #0 then fail else
      if p = #2 * scale then &norm scale values else
      if p = #0 then
        let maximum := (rec visit xs acc := case! xs
          | inl(u) => acc
          | inr(q) =>
            let x := &Numeric.abs (fst(q));
            visit (snd(q)) (if acc < x then x else acc));
        maximum values #0
      else
        let powers := &map (fun x,
          let a := &Numeric.abs x;
          if a = #0 then #0 else &Numeric.pow scale a p) values;
        let total := &Occil.sumInts powers;
        if total = #0 then #0 else &Numeric.pow scale total (&Numeric.div scale scale p)

/-- Generalized normal coordinate used by the source's p-sphere construction. -/
@[pl_fold] def exponentialPower : Exp rT := pl%
  fun scale p u,
    if p < #0 then fail else
    if p = #0 then &uniformRange scale (-scale) scale #() else
    if p = #2 * scale then &Numerical.normal scale #0 scale #() else
      let inverse := &Numeric.div scale scale p;
      let g := &Numerical.gamma scale inverse scale #();
      let magnitude := (if g = #0 then #0 else &Numeric.pow scale g inverse);
      if &Occil.fairCoin #() then magnitude else -magnitude

/-- Source normalized-EPD construction; p=0 selects its infinity-norm case.
Euclidean normalization retains 32 guard bits through sqrt and rounds only final
coordinates, preventing tiny proposal vectors from amplifying grid error.
Other p values first rescale by the exact maximum coordinate for the same reason. -/
@[pl_fold] def sphere : Exp rT := pl%
  rec draw scale dimensions radius p u :=
    if (dimensions <= #0) || (radius < #0) || (p < #0) then fail else
      let coordinates := &Occil.repeatSample (fun u, &exponentialPower scale p #()) dimensions;
      let maximum := &pNorm scale coordinates #0;
      if maximum = #0 then draw scale dimensions radius p #() else
        if p = #2 * scale then
          let guard := #4294967296;
          let distance := &Numeric.sqrt #1 (&integerSquares coordinates * guard * guard);
          &map (fun x, radius * x * guard / distance) coordinates
        else
          let rescaled := &map (fun x, x * scale / maximum) coordinates;
          let distance := &pNorm scale rescaled p;
          &map (fun x, radius * x / distance) rescaled

/-- Uniform p-ball by an independent radius U^(1/d), avoiding a normalization
convention mismatch between standard normals and rate-one exponentials. -/
@[pl_fold] def ball : Exp rT := pl%
  fun scale dimensions radius p u,
    if (dimensions <= #0) || (radius < #0) then fail else
      let exponent := scale / dimensions;
      let radial := &Numeric.pow scale (&Numeric.uniform scale #()) exponent;
      &sphere scale dimensions (&Numeric.mul scale radius radial) p #()

/-- EPD/exponential construction of a uniform finite-p ball. The p=2
normal branch needs twice a unit exponential, matching its variance-one normal
coordinates; the generic gamma-powered EPD branch uses one unit exponential. -/
@[pl_fold] def ballEPD : Exp rT := pl%
  rec draw scale dimensions radius p u :=
    if (dimensions <= #0) || (radius < #0) || (p <= #0) then fail else
      let coordinates := &Occil.repeatSample (fun u, &exponentialPower scale p #()) dimensions;
      let e := &Numerical.exponential scale scale #();
      if p = #2 * scale then
        let guard := #4294967296;
        let squares := &integerSquares coordinates + #2 * e * scale;
        let denominator := &Numeric.sqrt #1 (squares * guard * guard);
        if denominator <= #0 then draw scale dimensions radius p #() else
          &map (fun x, radius * x * guard / denominator) coordinates
      else
        let distance := &pNorm scale coordinates p;
        let radialPower := (if distance = #0 then #0 else &Numeric.pow scale distance p);
        let denominator := &Numeric.pow scale (radialPower + e) (&Numeric.div scale scale p);
        if denominator <= #0 then draw scale dimensions radius p #() else
          &map (fun x, radius * x / denominator) coordinates

@[pl_fold] def shell : Exp rT := pl%
  fun scale dimensions inner outer p u,
    if (dimensions <= #0) || (inner < #0) || (outer <= inner) then fail else
      let a := (if inner = #0 then #0 else &Numeric.pow scale inner (dimensions * scale));
      let b := &Numeric.pow scale outer (dimensions * scale);
      let v := a + &Numeric.mul scale (b - a) (&Numeric.uniform scale #());
      let radius := &Numeric.pow scale v (scale / dimensions);
      &sphere scale dimensions radius p #()

@[pl_fold] def box : Exp rT := pl%
  rec draw scale lower upper u := case! lower
    | inl(v) => case! upper | inl(w) => inl(#()) | inr(q) => fail
    | inr(p) => case! upper | inl(w) => fail | inr(q) =>
      inr((&uniformRange scale (fst(p)) (fst(q)) #(), draw scale (snd(p)) (snd(q)) #()))

@[pl_fold] def hypercube : Exp rT := pl%
  fun scale dimensions lower upper u,
    if dimensions < #0 then fail else
      &Occil.repeatSample (fun u, &uniformRange scale lower upper #()) dimensions

/-- Three-dimensional cone whose tip is at z=0 and base at z=height. -/
@[pl_fold] def cone : Exp rT := pl%
  fun scale height radius u,
    if (height <= #0) || (radius < #0) then fail else
      let a := &Numeric.uniform scale #();
      let b := &Numeric.uniform scale #();
      let c := &Numeric.uniform scale #();
      let ab := (if a < b then b else a);
      let z := &Numeric.mul scale height (if ab < c then c else ab);
      let localRadius := &Numeric.div scale (&Numeric.mul scale radius z) height;
      let xy := &ball scale #2 localRadius (#2 * scale) #();
      inr((&Occil.getAt xy #0, inr((&Occil.getAt xy #1, inr((z, inl(#())))))))

@[pl_fold] def cylinder : Exp rT := pl%
  fun scale height radius u,
    let xy := &ball scale #2 radius (#2 * scale) #();
    let z := &uniformRange scale #0 height #();
    inr((&Occil.getAt xy #0, inr((&Occil.getAt xy #1, inr((z, inl(#())))))))

@[pl_fold] def circle : Exp rT := pl%
  fun scale radius u,
    if radius < #0 then fail else
      let angle := &Numeric.mul scale (#2 * &Numeric.pi scale) (&Numeric.uniform scale #());
      (&Numeric.mul scale radius (&Numeric.cos scale angle),
       &Numeric.mul scale radius (&Numeric.sin scale angle))

/-- Lateral surface of a cylinder, excluding its two end caps. -/
@[pl_fold] def cylinderSurface : Exp rT := pl%
  fun scale height radius u,
    let xy := &circle scale radius #();
    let z := &uniformRange scale #0 height #();
    inr((fst(xy), inr((snd(xy), inr((z, inl(#())))))))

/-- Reflect a selected coordinate into the positive half-space. -/
@[pl_fold] def positiveCoordinate : Exp rT := pl%
  rec reflect coordinates index := case! coordinates
    | inl(v) => fail
    | inr(p) => if index = #0 then inr((&Numeric.abs (fst(p)), snd(p))) else
      inr((fst(p), reflect (snd(p)) (index - #1)))

@[pl_fold] def halfSphere : Exp rT := pl%
  fun scale dimensions radius p coordinate u,
    &positiveCoordinate (&sphere scale dimensions radius p #()) coordinate

@[pl_fold] def halfBall : Exp rT := pl%
  fun scale dimensions radius p coordinate u,
    &positiveCoordinate (&ball scale dimensions radius p #()) coordinate

@[pl_fold] def halfShell : Exp rT := pl%
  fun scale dimensions inner outer p coordinate u,
    &positiveCoordinate (&shell scale dimensions inner outer p #()) coordinate

/-- Latitude/longitude in radians; latitude is asin(U), U uniform on (-1,1). -/
@[pl_fold] def latitudeLongitude : Exp rT := pl%
  fun scale u,
    let pi := &Numeric.pi scale;
    let longitude := &uniformRange scale (-pi) pi #();
    let x := &uniformRange scale (-scale) scale #();
    let denominator := &Numeric.sqrt scale (scale - &Numeric.mul scale x x);
    let latitude := &Numeric.atan scale (&Numeric.div scale x denominator);
    (latitude, longitude)

/-- Uniform barycentric point in the simplex spanned by the supplied vertices. -/
@[pl_fold] def simplex : Exp rT := pl%
  fun scale vertices u,
    let count := &Occil.length vertices;
    if count <= #0 then fail else
      let dimensions := &Occil.length (&Occil.getAt vertices #0);
      if dimensions + #1 < count then fail else
        let weights := &dirichlet scale (&constants count scale) #();
        let accumulate := (rec addPoints points fractions total := case! points
          | inl(v) => total
          | inr(p) => case! fractions | inl(v) => fail | inr(q) =>
            addPoints (snd(p)) (snd(q))
              (&add total (&scaleVector scale (fst(q)) (fst(p)))));
        accumulate vertices weights (&zeros dimensions)

/-- Fast triangle construction using max(U,V), as in the source article. -/
@[pl_fold] def triangle : Exp rT := pl%
  fun scale a b c u,
    let first := &Numeric.uniform scale #();
    let second := &Numeric.uniform scale #();
    let radial := (if first < second then second else first);
    let split := &Numeric.uniform scale #();
    let wb := &Numeric.mul scale radial (scale - split);
    let wc := &Numeric.mul scale radial split;
    &add (&scaleVector scale (scale - radial) a)
      (&add (&scaleVector scale wb b) (&scaleVector scale wc c))

/-- Uniform ellipsoid surface via sphere proposals and the surface-area Jacobian.
Axes must be positive; covariance scaling alone would bias the surface measure. -/
@[pl_fold] def ellipsoidSurface : Exp rT := pl%
  rec draw scale axes u :=
    let n := &Occil.length axes;
    let minimum := (rec visit xs acc := case! xs | inl(v) => acc | inr(p) =>
      if (fst(p)) <= #0 then fail else visit (snd(p)) (if (fst(p)) < acc then fst(p) else acc));
    if n <= #0 then fail else
      let smallest := minimum axes (&Occil.getAt axes #0);
      let point := &sphere scale n scale (#2 * scale) #();
      let divideAxes := (rec divide xs ys := case! xs | inl(v) => inl(#()) | inr(p) =>
        case! ys | inl(v) => fail | inr(q) =>
          inr((&Numeric.div scale (fst(p)) (fst(q)), divide (snd(p)) (snd(q)))));
      let probability := &Numeric.mul scale smallest (&norm scale (divideAxes point axes));
      if &Numeric.uniform scale #() <= probability then
        let multiplyAxes := (rec multiply xs ys := case! xs | inl(v) => inl(#()) | inr(p) =>
          case! ys | inl(v) => fail | inr(q) =>
            inr((&Numeric.mul scale (fst(p)) (fst(q)), multiply (snd(p)) (snd(q)))));
        multiplyAxes point axes
      else draw scale axes #()

/-- Lacko–Harman radial family; shape=0 is concentrated on the p-sphere. -/
@[pl_fold] def betaBall : Exp rT := pl%
  fun scale dimensions radius p shape u,
    if (dimensions <= #0) || (p <= #0) || (shape < #0) then fail else
      if shape = #0 then &sphere scale dimensions radius p #() else
        let a := &Numeric.div scale (dimensions * scale) p;
        let b := &Numeric.div scale shape p;
        let beta := &Numerical.beta scale a b #();
        let radial := (if beta = #0 then #0 else &Numeric.pow scale beta (&Numeric.div scale scale p));
        &sphere scale dimensions (&Numeric.mul scale radius radial) p #()

end Occil.Multivariate
