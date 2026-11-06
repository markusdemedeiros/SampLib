import SampLib.Uniform.RationalCoin
import Samplers.Discrete.Counts

/-! # Closedness of the inverse-urn source used by its rational wrappers -/

open ProbLang

namespace SampLib.InversePolya

theorem inversePolya_fv {rT : Type _} :
    (Occil.DiscreteExtra.inversePolya : Exp rT).fv = ∅ := by
  simp [Occil.DiscreteExtra.inversePolya, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem inversePolya_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.inversePolya = Occil.DiscreteExtra.inversePolya :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem inversePolya_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.inversePolya : Exp rT) =
      Occil.DiscreteExtra.inversePolya :=
  Exp.closeRec_fresh x _ k (by simp [inversePolya_fv])

end SampLib.InversePolya
