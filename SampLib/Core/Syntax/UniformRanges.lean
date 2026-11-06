import SampLib.Uniform.RndIntExcRange

/-! Closedness facts for composing the integer-range samplers. -/

open ProbLang

namespace SampLib.RndIntExcRange

theorem rndIntExcRange_lc {rT : Type _} :
    (Occil.rndIntExcRange : Exp rT).IsLocallyClosed := by is_lc

theorem rndIntExcRange_fv {rT : Type _} :
    (Occil.rndIntExcRange : Exp rT).fv = ∅ := by
  simp [Occil.rndIntExcRange, Occil.uniformInt, Exp.fv]

@[simp] theorem rndIntExcRange_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rndIntExcRange = Occil.rndIntExcRange :=
  (Exp.open_lc k e _ rndIntExcRange_lc).symm

@[simp] theorem rndIntExcRange_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rndIntExcRange : Exp rT) = Occil.rndIntExcRange :=
  Exp.closeRec_fresh x _ k (by simp [rndIntExcRange_fv])

end SampLib.RndIntExcRange
