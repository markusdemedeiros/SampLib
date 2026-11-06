import SampLib.Samplers.LinearFactory

/-! # Closed syntax of the adaptive linear factory -/

open ProbLang

namespace SampLib.LinearFactorySyntax

def value {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.linear, .fix (by is_lc), by is_lc⟩

theorem value_fst {rT : Type} : (value (rT := rT)).fst = Occil.FactoryExtra.linear := rfl

theorem linear_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.linear = Occil.FactoryExtra.linear :=
  (Exp.open_lc k e _ (value (rT := rT)).lc).symm

theorem linear_fv {rT : Type} : (Occil.FactoryExtra.linear : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.linear, Occil.FactoryExtra.gambler,
    Occil.FactoryExtra.highPowerLogistic, Occil.logisticFactory,
    Exp.fv, RationalCoin.rationalCoin_fv]

theorem linear_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.linear : Exp rT) = Occil.FactoryExtra.linear :=
  Exp.closeRec_fresh x _ k (by simp [linear_fv])

end SampLib.LinearFactorySyntax
