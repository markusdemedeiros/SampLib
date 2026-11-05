import Samplers.Multivariate.Geometry
import Samplers.Multivariate.Stable

/-! Numerical copulas and multivariate distribution transformations. Lists of
quantile functions permit non-Gaussian marginals without new language primitives. -/
namespace Occil.Multivariate
open ProbLang
variable {rT : Type _}

/-- Gaussian copula from any positive-definite covariance matrix. Each
coordinate is standardized by its own marginal standard deviation. -/
@[pl_fold] def gaussianCopula : Exp rT := pl%
  fun scale covariance u,
    let values := &normal scale (inl(#())) covariance #();
    let convert := (rec standardize xs i := case! xs | inl(v) => inl(#()) | inr(q) =>
      let variance := &Occil.getAt (&Occil.getAt covariance i) i;
      let standardized := &Numeric.div scale (fst(q)) (&Numeric.sqrt scale variance);
      let p := &Numeric.normalCDF scale standardized;
      let value := (if p <= #0 then #1 else if scale <= p then scale - #1 else p);
      inr((value, standardize (snd(q)) (i + #1))));
    convert values #0

@[pl_fold] def productCopula : Exp rT := pl%
  fun scale dimensions u,
    if dimensions < #0 then fail else &Occil.repeatSample (fun u, &Numeric.uniform scale #()) dimensions

@[pl_fold] def upperBoundCopula : Exp rT := pl%
  fun scale dimensions u,
    if dimensions < #0 then fail else &constants dimensions (&Numeric.uniform scale #())

/-- The Frechet lower bound is a copula only in dimension two. -/
@[pl_fold] def lowerBoundCopula : Exp rT := pl%
  fun scale u,
    let x := &Numeric.uniform scale #();
    inr((x, inr((scale - x, inl(#())))))

@[pl_fold] def transformMarginals : Exp rT := pl%
  rec transform uniforms quantiles := case! uniforms
    | inl(u) => case! quantiles | inl(v) => inl(#()) | inr(q) => fail
    | inr(p) => case! quantiles | inl(v) => fail | inr(q) =>
      inr(((fst(q)) (fst(p)), transform (snd(p)) (snd(q))))

/-- Gaussian-copula dependence followed by arbitrary quantile callbacks. -/
@[pl_fold] def normalToAnything : Exp rT := pl%
  fun scale correlation quantiles u,
    &transformMarginals (&gaussianCopula scale correlation #()) quantiles

@[pl_fold] def correlatedExponential : Exp rT := pl%
  fun scale rho rate1 rate2 u,
    let pair := &binormal scale #0 #0 scale scale rho #();
    let a := &Numeric.normalCDF scale (fst(pair));
    let b := &Numeric.normalCDF scale (snd(pair));
    if (rate1 <= #0) || (rate2 <= #0) then fail else
      let ua := (if a <= #0 then #1 else if scale <= a then scale - #1 else a);
      let ub := (if b <= #0 then #1 else if scale <= b then scale - #1 else b);
      (&Numeric.div scale (-(&Numeric.log scale ua)) rate1,
       &Numeric.div scale (-(&Numeric.log scale ub)) rate2)

/-- Bivariate T-Poisson hierarchy with Gaussian/exponential latent dependence. -/
@[pl_fold] def poissonHierarchy : Exp rT := pl%
  fun scale rho rate1 rate2 lambda1 lambda2 u,
    if (lambda1 < #0) || (lambda2 < #0) then fail else
      let latent := &correlatedExponential scale rho rate1 rate2 #();
      (&Occil.poissonRational (&Numeric.mul scale lambda1 (fst(latent))) scale,
       &Occil.poissonRational (&Numeric.mul scale lambda2 (snd(latent))) scale)

/-- N-dimensional copula/quantile Poisson hierarchy. Each latent margin has
its supplied quantile function; each Poisson intensity has a separate lambda. -/
@[pl_fold] def poissonHierarchyND : Exp rT := pl%
  fun scale covariance quantiles lambdas u,
    let latent := &normalToAnything scale covariance quantiles #();
    let draw := (rec generate xs rates := case! xs
      | inl(v) => case! rates | inl(w) => inl(#()) | inr(q) => fail
      | inr(p) => case! rates | inl(w) => fail | inr(q) =>
        let mean := &Numeric.mul scale (fst(p)) (fst(q));
        inr((&Occil.poissonRational mean scale, generate (snd(p)) (snd(q)))));
    draw latent lambdas

/-- Multivariate Student t: one shared chi-square divisor creates tail dependence. -/
@[pl_fold] def studentT : Exp rT := pl%
  rec draw scale degrees means covariance u :=
    if degrees <= #0 then fail else
      let chi := &Numerical.gamma scale (degrees / #2) (scale / #2) #();
      if chi <= #0 then draw scale degrees means covariance #() else
        let center := (if &Occil.length means = #0 then &zeros (&Occil.length covariance) else means);
        &add center (&scaleVector scale (&Numeric.sqrt scale (&Numeric.div scale degrees chi))
          (&normal scale (inl(#())) covariance #()))

/-- Midpoint quadrature for the Student CDF, using the cosine-integral identity.
The 128-panel numerical integration is an approximation, especially for tiny df. -/
@[pl_fold] def studentCDF : Exp rT := pl%
  fun scale degrees x,
    if degrees <= #0 then fail else if #100 * scale < degrees then &Numeric.normalCDF scale x else
      let theta := &Numeric.atan scale (&Numeric.div scale (&Numeric.abs x) (&Numeric.sqrt scale degrees));
      let halfPi := &Numeric.pi scale / #2;
      let integrate := (fun limit,
        let loop := (rec sum i acc := if i = #128 then &Numeric.mul scale (limit / #128) acc else
          let angle := limit * (#2 * i + #1) / #256;
          let c := &Numeric.cos scale angle;
          let value := (if c <= #0 then #0 else &Numeric.pow scale c (degrees - scale));
          sum (i + #1) (acc + value));
        loop #0 #0);
      let numerator := integrate theta;
      let denominator := integrate halfPi;
      let shift := &Numeric.div scale numerator (#2 * denominator);
      if x < #0 then scale / #2 - shift else scale / #2 + shift

@[pl_fold] def studentTCopula : Exp rT := pl%
  fun scale degrees covariance u,
    let n := &Occil.length covariance;
    let values := &studentT scale degrees (&zeros n) covariance #();
    let convert := (rec standardize xs i := case! xs | inl(v) => inl(#()) | inr(q) =>
      let variance := &Occil.getAt (&Occil.getAt covariance i) i;
      let x := &Numeric.div scale (fst(q)) (&Numeric.sqrt scale variance);
      let p := &studentCDF scale degrees x;
      let value := (if p <= #0 then #1 else if scale <= p then scale - #1 else p);
      inr((value, standardize (snd(q)) (i + #1))));
    convert values #0

/-- Marshall-Olkin frailty construction for a completely monotone Archimedean
Laplace generator. mixer returns its nonnegative frailty; generator is its LT. -/
@[pl_fold] def archimedeanCopula : Exp rT := pl%
  rec draw scale dimensions mixer generator u :=
    let frailty := mixer #();
    if frailty <= #0 then draw scale dimensions mixer generator #() else
      &Occil.repeatSample (fun u,
        generator (&Numeric.div scale (&Numerical.exponential scale scale #()) frailty)) dimensions

@[pl_fold] def claytonCopula : Exp rT := pl%
  fun scale dimensions theta u,
    if theta <= #0 then fail else
      let inverse := &Numeric.div scale scale theta;
      &archimedeanCopula scale dimensions
        (fun u, &Numerical.gamma scale inverse scale #())
        (fun t, &Numeric.pow scale (scale + t) (-inverse)) #()

/-- Elliptical family with an independent radius callback and covariance shape. -/
@[pl_fold] def elliptical : Exp rT := pl%
  fun scale means covariance radiusSampler u,
    let radius := radiusSampler #();
    &covarianceTransform scale means covariance
      (&sphere scale (&Occil.length covariance) radius (#2 * scale) #())

@[pl_fold] def beckmann : Exp rT := pl%
  fun scale mu1 mu2 sigma1 sigma2 rho u,
    let pair := &binormal scale mu1 mu2 sigma1 sigma2 rho #();
    &norm scale (inr((fst(pair), inr((snd(pair), inl(#()))))))

@[pl_fold] def rice : Exp rT := pl%
  fun scale noncentrality sigma u,
    let center := &Numeric.div scale noncentrality (&Numeric.sqrt scale (#2 * scale));
    &beckmann scale center center sigma sigma #0 #()

@[pl_fold] def riceNorton : Exp rT := pl%
  fun scale a b m u,
    if m <= #0 then fail else
      let center := &Numeric.div scale a (&Numeric.sqrt scale (#2 * m));
      let sigma := &Numeric.sqrt scale (&Numeric.div scale (&Numeric.mul scale b b) m);
      let xyz := &Occil.repeatSample (fun u, &Numerical.normal scale center sigma #()) #3;
      &norm scale xyz

@[pl_fold] def complexNormal : Exp rT := pl%
  fun scale u,
    let sigma := &Numeric.sqrt scale (scale / #2);
    &binormal scale #0 #0 sigma sigma #0 #()


/-- Gumbel-Hougaard copula, theta>=1, using a positive stable frailty. -/
@[pl_fold] def gumbelCopula : Exp rT := pl%
  fun scale dimensions theta u,
    if theta < scale then fail else
      if theta = scale then &productCopula scale dimensions #() else
        let alpha := &Numeric.div scale scale theta;
        let halfAngle := &Numeric.mul scale alpha (&Numeric.pi scale / #2);
        let correction := &Numeric.pow scale (&Numeric.cos scale halfAngle) theta;
        &archimedeanCopula scale dimensions
          (fun u, &Numeric.mul scale correction (&stable scale alpha scale #()))
          (fun t, &Numeric.exp scale (-(&Numeric.pow scale t alpha))) #()

/-- Exchangeable binary labels with the prescribed count weights. -/
@[pl_fold] def exchangeableLabels : Exp rT := pl%
  fun weights,
    let dimensions := &Occil.length weights - #1;
    if dimensions <= #0 then fail else
      let ones := &Occil.weightedChoice weights;
      &Occil.shuffle ((let labels := (rec build n := if n = #0 then &constants (dimensions - ones) #0
        else inr((#1, build (n - #1)))); labels ones))

/-- Literal max/min recipe printed in exporand.html. Its outputs generally do
not have uniform marginals; this is separate from the corrected copula below. -/
@[pl_fold] def exchangeableFGMSource : Exp rT := pl%
  fun scale weights u,
    let labels := &exchangeableLabels weights;
    &map (fun label,
      let a := &Numeric.uniform scale #();
      let b := &Numeric.uniform scale #();
      let c := &Numeric.uniform scale #();
      let maximum := (if a < b then b else a);
      if label = #0 then maximum else if c < maximum then c else maximum) labels

/-- FGM latent-bit construction: sqrt(V)*W^I. Replacing the displayed
min(max(U1,U2),U3) with max(U1,U2)*U3 gives uniform margins when the count
weights satisfy E[count]=dimensions/2. That balance is checked exactly. -/
@[pl_fold] def exchangeableFGMCopula : Exp rT := pl%
  fun scale weights u,
    let dimensions := &Occil.length weights - #1;
    let total := &Occil.sumInts weights;
    let moment := (rec sum xs i := case! xs | inl(v) => #0 | inr(p) =>
      i * (fst(p)) + sum (snd(p)) (i + #1));
    if #2 * moment weights #0 = dimensions * total then
      let labels := &exchangeableLabels weights;
      &map (fun label,
        let a := &Numeric.uniform scale #();
        let b := &Numeric.uniform scale #();
        let maximum := (if a < b then b else a);
        if label = #0 then maximum else &Numeric.mul scale maximum (&Numeric.uniform scale #())) labels
    else fail

end Occil.Multivariate
