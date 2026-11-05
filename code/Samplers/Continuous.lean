import Samplers.Bernoulli.Basic
import Samplers.Data

/-! Comparison/addition-only continuous sampling. Sources: randomfunc.html
(exponential, mixtures, transforms, order statistics), randomnotes.html (Karney
normal), bernoulli.html (exponential Bernoulli trials). All terms are generic in
rT, so the same syntax is executable at Float and can be specified at real ℝ. -/
namespace Occil

open ProbLang

variable {rT : Type _}

/-- Number of strict decreases below x. -/
@[pl_fold] def decreasingTrial : Exp rT := pl%
  rec trial n x := let y := urand;
    if y < x then trial (n + #1) y else n

/-- Von Neumann unit-rate exponential: restart on odd decreasing-chain length. -/
@[pl_fold] def exponential : Exp rT := pl%
  fun u,
    let loop := (rec draw whole :=
      let x := urand;
      let n := &decreasingTrial #0 x;
      if n % #2 = #0 then toReal(whole) + x else draw (whole + #1));
    loop #0

/-- Laplace(0,1) from an independent exponential and sign. -/
@[pl_fold] def laplace : Exp rT := pl%
  fun u, let x := &exponential #(); if &fairCoin #() then x else -x

/-- Gamma with positive integer shape and unit rate. -/
@[pl_fold] def erlang : Exp rT := pl%
  rec draw shape := if shape <= #0 then fail else
    if shape = #1 then &exponential #() else &exponential #() + draw (shape - #1)

@[pl_fold] def uniformSum : Exp rT := pl%
  rec draw n := if n < #0 then fail else if n = #0 then toReal(#0) else
    let x := urand;
    x + draw (n - #1)

@[pl_fold] def uniformMin : Exp rT := pl%
  fun u, let x := urand; let y := urand; if x < y then x else y

@[pl_fold] def uniformMax : Exp rT := pl%
  fun u, let x := urand; let y := urand; if x < y then y else x

/-- k-th smallest among n uniforms, 1<=k<=n: Beta(k,n+1-k). -/
@[pl_fold] def orderStatistic : Exp rT := pl%
  fun n k,
    if (n <= #0) || (k <= #0) || (n < k) then fail else
      let build := (rec go remaining := if remaining = #0 then inl(#()) else
        let x := urand;
        &insertReal x (go (remaining - #1)));
      &getAt (build n) (k - #1)

/-- A mixture of two abstract samplers selected by a coin callback. -/
@[pl_fold] def mixture : Exp rT := pl%
  fun coin left right u, if coin #() then left #() else right #()

/-! Karney's Gaussian decomposition. These are explicit pl% terms, following the
same algorithm as upstream Code/Samplers, rather than calling gauss/sample as an oracle. -/

@[pl_fold] def expHalfCoin [ProbLangℝ rT] : Exp rT := pl%
  fun u,
    let x := urand;
    if x <= #real (ProbLangℝ.realOfRat (1 / 2)) then
      &decreasingTrial #0 x % #2 = #1
    else #true

@[pl_fold] def iterateCoin : Exp rT := pl%
  rec trial coin n := if n = #0 then #true else
    if coin #() then trial coin (n - #1) else #false

@[pl_fold] def geometricFailures : Exp rT := pl%
  rec draw coin n := if coin #() then draw coin (n + #1) else n

@[pl_fold] def gaussianSelectorC : Exp rT := pl%
  fun m, let v := rand(m + #2, #()); if v = #0 then #0 else if v = #1 then #1 else #2

@[pl_fold] def gaussianSelectorCoin : Exp rT := pl%
  fun k x u,
    let c := &gaussianSelectorC (#2 * k);
    let r := urand;
    if c = #0 then #true else if c = #1 then x < r else #false

@[pl_fold] def gaussianSelector : Exp rT := pl%
  fun k x,
    let loop := (rec trial y n :=
      let z := urand;
      if y < z then n else
        if &gaussianSelectorCoin k x #() then n else trial z (n + #1));
    loop x #0 % #2 = #0

@[pl_fold] def gaussianInteger [ProbLangℝ rT] : Exp rT := pl%
  rec draw u :=
    let k := &geometricFailures &expHalfCoin #0;
    if &iterateCoin &expHalfCoin (k * (k - #1)) then k else draw #()

@[pl_fold] def gaussian [ProbLangℝ rT] : Exp rT := pl%
  fun u,
    let loop := (rec draw u :=
      let k := &gaussianInteger #();
      let x := urand;
      if &iterateCoin (fun u, &gaussianSelector k x) (k + #1) then
        x + toReal(k)
      else draw #());
    let y := loop #();
    if &fairCoin #() then -y else y

end Occil
