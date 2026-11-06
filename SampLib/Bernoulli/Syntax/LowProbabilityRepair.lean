import SampLib.Bernoulli.Support.LinearFactorySyntax
import SampLib.Core.Syntax.ClosedExp

/-! # Proposed low-probability factory repair

This records the reviewed inner half-margin repair. The canonical sampler is
definitionally equal to this term, as checked in `Samplers/LinearLowProbability`.
-/

open ProbLang

namespace SampLib.LowProbabilityRepair

namespace Syntax

scoped instance rational_closed {rT : Type} :
    ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := RationalCoin.rationalCoin_fv

scoped instance logistic_closed {rT : Type} :
    ClosedExp (Occil.logisticFactory : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.logisticFactory, Exp.fv, RationalCoin.rationalCoin_fv]

scoped instance linear_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.linear : Exp rT) where
  lc := LinearFactorySyntax.value.lc
  fv := LinearFactorySyntax.linear_fv

end Syntax

@[pl_fold] def algorithm {rT : Type _} : Exp rT := pl%
  fun coin a b m n u,
    if (a < #0) || (b <= #0) || (m < #0) || (n <= #2 * m) then fail else
    if a <= b then
      if &Occil.rationalCoin a b then coin #() else #false
    else if m = #0 then #false else
      let betaDen := n - #2 * m;
      if &Occil.logisticFactory coin (a * n) (b * betaDen) #() then
        if &Occil.rationalCoin betaDen n then #true else
          &Occil.FactoryExtra.linear coin (a * n) (b * #2 * m) #1 #2 #()
      else #false

namespace Syntax

/-- Finalize the inner binder before inserting the arbitrary callback value. -/
def body {rT : Type} (coin : Val rT) (a b m n : ℤ) : Exp rT :=
  let branch : Exp rT := pl%
    if &Occil.logisticFactory &coin.fst (#int a * #int n)
        (#int b * {Exp.bvar 0}) #() then
      if &Occil.rationalCoin {Exp.bvar 0} #int n then #true else
        &Occil.FactoryExtra.linear &coin.fst (#int a * #int n)
          (#int b * #2 * #int m) #1 #2 #()
    else #false
  let expanding := Exp.app (.lam branch) pl(#int n - #2 * #int m)
  pl% if (#int a < #0) || (#int b <= #0) || (#int m < #0) || (#int n <= #2 * #int m)
    then fail else
    if #int a <= #int b then
      if &Occil.rationalCoin #int a #int b then &coin.fst #() else #false
    else if #int m = #0 then #false else &expanding

end Syntax

end SampLib.LowProbabilityRepair
