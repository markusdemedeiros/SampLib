import SampLib.Samplers.RationalPower
import SampLib.Samplers.RationalCoin

/-! # Closed power-factory constants under sampler binders -/

open ProbLang

namespace SampLib.RationalPowerCoinSyntax

variable {rT : Type _}

theorem lc : (Occil.DiscreteExtra.rationalPowerCoin : Exp rT).IsLocallyClosed := by is_lc

theorem fv : (Occil.DiscreteExtra.rationalPowerCoin : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.rationalPowerCoin, Occil.iterateCoin, Occil.fractionalPower,
    Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.rationalPowerCoin =
      Occil.DiscreteExtra.rationalPowerCoin :=
  (Exp.open_lc k e _ lc).symm

@[simp] theorem closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.rationalPowerCoin : Exp rT) =
      Occil.DiscreteExtra.rationalPowerCoin :=
  Exp.closeRec_fresh x _ k (by simp [fv])

end SampLib.RationalPowerCoinSyntax
