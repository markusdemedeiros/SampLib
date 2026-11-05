import Samplers.Multivariate.Copulas
import Samplers.Multivariate.Stable

/-! Absorbing Markov-chain phase-type samplers and remaining covariance
mixtures from randomnotes.html. Eventual absorption is a parameter precondition.
Subgenerator entries, starting probabilities and rewards are scaled integers. -/
namespace Occil.Multivariate
open ProbLang
variable {rT : Type _}

@[pl_fold] def append : Exp rT := pl%
  rec join left right := case! left
    | inl(u) => right
    | inr(p) => inr((fst(p), join (snd(p)) right))

/-- Convert each subgenerator row into integer transition weights, appending
absorption. Common division by the departure rate cancels in weighted choice. -/
@[pl_fold] def generatorTransitions : Exp rT := pl%
  fun generator,
    let n := &Occil.length generator;
    let rows := (rec convert matrix i := case! matrix
      | inl(u) => inl(#())
      | inr(p) =>
        let row := fst(p);
        if &Occil.length row = n then
          let diagonal := &Occil.getAt row i;
          let total := &Occil.sumInts row;
          if (#0 <= diagonal) || (#0 < total) then fail else
            let offDiagonal := (rec entries xs j := case! xs
              | inl(u) => inr((-total, inl(#())))
              | inr(q) =>
                if j = i then inr((#0, entries (snd(q)) (j + #1))) else
                if (fst(q)) < #0 then fail else
                  inr((fst(q), entries (snd(q)) (j + #1))));
            inr((offDiagonal row #0, convert (snd(p)) (i + #1)))
        else fail);
    if n <= #0 then fail else rows generator #0

/-- Initial subprobability vector, with the residual assigned to immediate absorption. -/
@[pl_fold] def initialPhase : Exp rT := pl%
  fun scale probabilities states,
    let total := &Occil.sumInts probabilities;
    if (&Occil.length probabilities = states) && (total <= scale) then
      &Occil.weightedChoice (&append probabilities (inr((scale - total, inl(#())))))
    else fail

@[pl_fold] def phaseType : Exp rT := pl%
  fun scale probabilities generator u,
    let transitions := &generatorTransitions generator;
    let n := &Occil.length generator;
    let start := &initialPhase scale probabilities n;
    let loop := (rec visit state total := if n <= state then total else
      let rate := -(&Occil.getAt (&Occil.getAt generator state) state);
      let holding := &Numerical.exponential scale rate #();
      let next := &Occil.weightedChoice (&Occil.getAt transitions state);
      visit next (total + holding));
    loop start #0

@[pl_fold] def inhomogeneousPhaseType : Exp rT := pl%
  fun scale probabilities generator transform u,
    transform (&phaseType scale probabilities generator #())

/-- MPH* with deterministic nonnegative reward rates: accumulate holding*r_i
in every coordinate before following the common transient Markov chain. -/
@[pl_fold] def multivariatePhaseType : Exp rT := pl%
  fun scale probabilities generator rewards u,
    let n := &Occil.length generator;
    if (n <= #0) || (&Occil.length rewards = #0) then fail else
      let dimensions := &Occil.length (&Occil.getAt rewards #0);
      if (dimensions <= #0) || (&Occil.length rewards < n) then fail else
        let transitions := &generatorTransitions generator;
        let start := &initialPhase scale probabilities n;
        let loop := (rec visit state total := if n <= state then total else
          let rate := -(&Occil.getAt (&Occil.getAt generator state) state);
          let holding := &Numerical.exponential scale rate #();
          let updated := &add total (&scaleVector scale holding (&Occil.getAt rewards state));
          let next := &Occil.weightedChoice (&Occil.getAt transitions state);
          visit next updated);
        loop start (&zeros dimensions)

@[pl_fold] def addAt : Exp rT := pl%
  rec update values index amount := case! values
    | inl(u) => fail
    | inr(p) => if index = #0 then inr(((fst(p)) + amount, snd(p))) else
      inr((fst(p), update (snd(p)) (index - #1) amount))

/-- The article's displayed MPH pseudocode instead routes each holding time to
one randomly selected reward coordinate. This implements that distinct model. -/
@[pl_fold] def phaseTypeRandomRewards : Exp rT := pl%
  fun scale probabilities generator rewards u,
    let n := &Occil.length generator;
    if (n <= #0) || (&Occil.length rewards = #0) then fail else
      let dimensions := &Occil.length (&Occil.getAt rewards #0);
      let transitions := &generatorTransitions generator;
      let start := &initialPhase scale probabilities n;
      let loop := (rec visit state total := if n <= state then total else
        let rate := -(&Occil.getAt (&Occil.getAt generator state) state);
        let holding := &Numerical.exponential scale rate #();
        let coordinate := &Occil.weightedChoice (&Occil.getAt rewards state);
        let next := &Occil.weightedChoice (&Occil.getAt transitions state);
        visit next (&addAt total coordinate holding));
      loop start (&zeros dimensions)

@[pl_fold] def inhomogeneousMultivariatePhaseType : Exp rT := pl%
  fun scale probabilities generator rewards transforms u,
    &transformMarginals (&multivariatePhaseType scale probabilities generator rewards #()) transforms

@[pl_fold] def multivariateLinnik : Exp rT := pl%
  fun scale alpha covariance u,
    if (alpha <= #0) || (#2 * scale < alpha) then fail else
      let mixer := &geometricStable scale (alpha / #2) scale scale #();
      &scaleVector scale (&Numeric.sqrt scale (#2 * mixer))
        (&normal scale (inl(#())) covariance #())


/-- Literal multiplier shown in the article's multivariate-Linnik example.
The standard normal-variance-mixture construction above uses sqrt(2*mixer). -/
@[pl_fold] def multivariateLinnikSource : Exp rT := pl%
  fun scale alpha covariance u,
    if (alpha <= #0) || (#2 * scale < alpha) then fail else
      let mixer := &geometricStable scale (alpha / #2) scale scale #();
      &scaleVector scale mixer (&normal scale (inl(#())) covariance #())

@[pl_fold] def multivariateExponentialPower : Exp rT := pl%
  fun scale means covariance shape u,
    let dimensions := &Occil.length covariance;
    if shape <= #0 then fail else
      let g := &Numerical.gamma scale (&Numeric.div scale (dimensions * scale) shape) scale #();
      let radius := &Numeric.pow scale (#2 * g) (&Numeric.div scale scale shape);
      &covarianceTransform scale means covariance
        (&sphere scale dimensions radius (#2 * scale) #())

end Occil.Multivariate
