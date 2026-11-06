import SampLib.Discrete.Support.BinomialHalfRejectionSyntax

/-! # Closed outer branches of the half-binomial sampler -/

open ProbLang

namespace SampLib.BinomialHalfRejectionSyntax

variable {rT : Type _}

theorem sqrt_lc : (Occil.DiscreteExtra.integerSqrt : Exp rT).IsLocallyClosed := by is_lc

theorem sqrt_fv : (Occil.DiscreteExtra.integerSqrt : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.integerSqrt, Exp.fv]

@[simp] theorem sqrt_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.integerSqrt = Occil.DiscreteExtra.integerSqrt :=
  (Exp.open_lc k e _ sqrt_lc).symm

@[simp] theorem sqrt_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.integerSqrt : Exp rT) =
      Occil.DiscreteExtra.integerSqrt :=
  Exp.closeRec_fresh x _ k (by simp [sqrt_fv])

theorem bits_lc : (Occil.DiscreteExtra.binomialHalfBits : Exp rT).IsLocallyClosed := by is_lc

theorem bits_fv : (Occil.DiscreteExtra.binomialHalfBits : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.binomialHalfBits, Exp.fv, UniformInt.uniformInt_fv, power_fv]

@[simp] theorem bits_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.binomialHalfBits = Occil.DiscreteExtra.binomialHalfBits :=
  (Exp.open_lc k e _ bits_lc).symm

@[simp] theorem bits_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.binomialHalfBits : Exp rT) =
      Occil.DiscreteExtra.binomialHalfBits :=
  Exp.closeRec_fresh x _ k (by simp [bits_fv])

end SampLib.BinomialHalfRejectionSyntax
