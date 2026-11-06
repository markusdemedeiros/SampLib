import SampLib.Combinatorial.Shuffle

/-! Closedness of Fisher–Yates under sampler binders. -/

open ProbLang

namespace SampLib.Shuffle

theorem shuffle_lc {rT : Type _} : (Occil.shuffle : Exp rT).IsLocallyClosed := by is_lc

theorem shuffle_fv {rT : Type _} : (Occil.shuffle : Exp rT).fv = ∅ := by
  simp [Occil.shuffle, Occil.length, Occil.fillArray, Occil.readArray, Occil.uniformInt, Exp.fv]

@[simp] theorem shuffle_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.shuffle = Occil.shuffle :=
  (Exp.open_lc k e _ shuffle_lc).symm

@[simp] theorem shuffle_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.shuffle : Exp rT) = Occil.shuffle :=
  Exp.closeRec_fresh x _ k (by simp [shuffle_fv])

end SampLib.Shuffle
