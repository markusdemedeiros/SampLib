import SampLib.Syntax.ClosedExp
import SampLib.UniformBagBracket
import Samplers.Constants.Engines

/-! Closedness of the positive-series engine, without unfolding it in consumers. -/

open ProbLang

namespace SampLib.FromPositiveSeries

theorem fromPositiveSeries_lc {rT : Type} :
    (Occil.Constants.fromPositiveSeries : Exp rT).IsLocallyClosed := by is_lc

theorem fromPositiveSeries_fv {rT : Type} :
    (Occil.Constants.fromPositiveSeries : Exp rT).fv = ∅ := by
  simp [Occil.Constants.fromPositiveSeries, Occil.newUniformBag,
    UniformBag.uniformBagLess_fv, Exp.fv]

instance fromPositiveSeries_closed {rT : Type} :
    ClosedExp (Occil.Constants.fromPositiveSeries : Exp rT) where
  lc := fromPositiveSeries_lc
  fv := fromPositiveSeries_fv

end SampLib.FromPositiveSeries
