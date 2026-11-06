import SampLib.Discrete.Support.RationalPowerCoinSyntax
import SampLib.Discrete.Support.IntegerPower
import SampLib.Discrete.Geometric

/-! # Closed integer and geometric constants in power-law samplers -/

open ProbLang

namespace SampLib.ZetaSyntax

variable {rT : Type _}

theorem geometric_fv : (Occil.geometric : Exp rT).fv = ∅ := by
  simp [Occil.geometric, Exp.fv]

@[simp] theorem geometric_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem geometric_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [geometric_fv])

theorem power_fv : (Occil.DiscreteExtra.integerPower : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.integerPower, Exp.fv]

@[simp] theorem power_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.integerPower = Occil.DiscreteExtra.integerPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem power_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.integerPower : Exp rT) =
      Occil.DiscreteExtra.integerPower :=
  Exp.closeRec_fresh x _ k (by simp [power_fv])

end SampLib.ZetaSyntax
