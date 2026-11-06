import SampLib.Discrete.Support.InversePolyaSyntax

/-! # Closedness of the rational beta-negative-binomial source -/

open ProbLang

namespace SampLib.BetaNegativeBinomial

theorem betaNegativeBinomial_fv {rT : Type _} :
    (Occil.DiscreteExtra.betaNegativeBinomial : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.betaNegativeBinomial, Exp.fv, InversePolya.inversePolya_fv]

@[simp] theorem betaNegativeBinomial_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.betaNegativeBinomial =
      Occil.DiscreteExtra.betaNegativeBinomial :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem betaNegativeBinomial_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.betaNegativeBinomial : Exp rT) =
      Occil.DiscreteExtra.betaNegativeBinomial :=
  Exp.closeRec_fresh x _ k (by simp [betaNegativeBinomial_fv])

end SampLib.BetaNegativeBinomial
