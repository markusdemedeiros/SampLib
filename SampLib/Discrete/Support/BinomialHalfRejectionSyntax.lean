import SampLib.Discrete.BinomialHalfBits
import SampLib.Discrete.Support.IntegerChoose
import SampLib.Discrete.Support.IntegerSqrt

/-! # Closed constants used under the half-binomial rejection loop -/

open ProbLang

namespace SampLib.BinomialHalfRejectionSyntax

variable {rT : Type _}

theorem geometric_lc : (Occil.geometric : Exp rT).IsLocallyClosed := by is_lc

theorem geometric_fv : (Occil.geometric : Exp rT).fv = ∅ := by
  simp [Occil.geometric, Exp.fv]

@[simp] theorem geometric_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ geometric_lc).symm

@[simp] theorem geometric_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [geometric_fv])

theorem choose_lc : (Occil.DiscreteExtra.choose : Exp rT).IsLocallyClosed := by is_lc

theorem choose_fv : (Occil.DiscreteExtra.choose : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.choose, Exp.fv]

@[simp] theorem choose_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.choose = Occil.DiscreteExtra.choose :=
  (Exp.open_lc k e _ choose_lc).symm

@[simp] theorem choose_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.choose : Exp rT) = Occil.DiscreteExtra.choose :=
  Exp.closeRec_fresh x _ k (by simp [choose_fv])

theorem power_lc : (Occil.DiscreteExtra.integerPower : Exp rT).IsLocallyClosed := by is_lc

theorem power_fv : (Occil.DiscreteExtra.integerPower : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.integerPower, Exp.fv]

@[simp] theorem power_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.integerPower = Occil.DiscreteExtra.integerPower :=
  (Exp.open_lc k e _ power_lc).symm

@[simp] theorem power_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.integerPower : Exp rT) =
      Occil.DiscreteExtra.integerPower :=
  Exp.closeRec_fresh x _ k (by simp [power_fv])

end SampLib.BinomialHalfRejectionSyntax
