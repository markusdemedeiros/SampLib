import SampLib.Core.Syntax.ClosedExp
import SampLib.Latent.UniformBagBracket
import Samplers.Constants.Exponential

/-! Closed source gateways under the binders of exponential factories. -/

open ProbLang

namespace SampLib.ExponentialTerms

scoped instance eBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.eBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.eBounds, Exp.fv]

scoped instance fromBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.fromBounds : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv]

scoped instance expMinusBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.expMinusBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.expMinusBounds, Exp.fv]

end SampLib.ExponentialTerms
