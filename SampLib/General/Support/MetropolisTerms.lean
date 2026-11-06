import SampLib.Uniform.RationalCoin
import Samplers.General.Core

/-! # Closedness of the Metropolis–Hastings program constant -/

open ProbLang

namespace SampLib.MetropolisTerms

theorem metropolisHastings_lc {rT : Type _} :
    (Occil.General.metropolisHastings : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem metropolisHastings_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.metropolisHastings = Occil.General.metropolisHastings :=
  (Exp.open_lc k e _ metropolisHastings_lc).symm

@[simp] theorem metropolisHastings_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.metropolisHastings : Exp rT) =
      Occil.General.metropolisHastings :=
  Exp.closeRec_fresh x _ k
    (by simp [Occil.General.metropolisHastings, Exp.fv, RationalCoin.rationalCoin_fv])

end SampLib.MetropolisTerms
