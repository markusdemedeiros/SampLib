import SampLib.Samplers.Rejection

/-! Closedness of generic rejection under sampler binders. -/

open ProbLang

namespace SampLib.Rejection

theorem rejection_lc {rT : Type*} : (Occil.rejection : Exp rT).IsLocallyClosed := by is_lc

theorem rejection_fv {rT : Type*} : (Occil.rejection : Exp rT).fv = ∅ := by
  simp [Occil.rejection, Exp.fv]

@[simp] theorem rejection_openRec {rT : Type*} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rejection = Occil.rejection :=
  (Exp.open_lc k e _ rejection_lc).symm

@[simp] theorem rejection_closeRec {rT : Type*} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rejection : Exp rT) = Occil.rejection :=
  Exp.closeRec_fresh x _ k (by simp [rejection_fv])

end SampLib.Rejection
