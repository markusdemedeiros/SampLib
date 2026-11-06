import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Basic

/-! # Source terms of the rational negative-exponential coin

The named sampler is closed, so substitution and abstraction leave it unchanged.
-/

open ProbLang

namespace SampLib.ExpMinusRational

def trial {rT : Type _} (a b : ℤ) : Exp rT := pl%
  rec go i parity :=
    if &Occil.rationalCoin #int a (#int b * i) then go (i + #1) (~parity)
    else parity

def small {rT : Type _} : Exp rT := pl%
  fun numerator denominator,
    let loop := (rec go i parity :=
      if &Occil.rationalCoin numerator (denominator * i) then go (i + #1) (~parity)
      else parity);
    loop #1 #true

theorem small_lc {rT : Type _} : (small : Exp rT).IsLocallyClosed := by is_lc

theorem small_fv {rT : Type _} : (small : Exp rT).fv = ∅ := by
  simp [small, Exp.fv, RationalCoin.rationalCoin_fv]

theorem small_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e small = small := (Exp.open_lc k e _ small_lc).symm

theorem small_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (small : Exp rT) = small :=
  Exp.closeRec_fresh x _ k (by simp [small_fv])

def whole {rT : Type _} : Exp rT := pl%
  rec rep n := if n = #0 then #true else
    if &small #1 #1 then rep (n - #1) else #false

/-- Closedness preserves the named sampler when it is used as a callback. -/
theorem expMinusRational_lc {rT : Type _} :
    (Occil.expMinusRational : Exp rT).IsLocallyClosed := by is_lc

theorem expMinusRational_fv {rT : Type _} :
    (Occil.expMinusRational : Exp rT).fv = ∅ := by
  simp [Occil.expMinusRational, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem expMinusRational_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.expMinusRational = Occil.expMinusRational :=
  (Exp.open_lc k e _ expMinusRational_lc).symm

@[simp] theorem expMinusRational_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.expMinusRational : Exp rT) = Occil.expMinusRational :=
  Exp.closeRec_fresh x _ k (by simp [expMinusRational_fv])

end SampLib.ExpMinusRational
