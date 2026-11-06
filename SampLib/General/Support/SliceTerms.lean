import SampLib.Common.Syntax.Rejection
import SampLib.Core.Syntax.UniformRanges
import Samplers.General.Core

/-! # Closedness of the finite-grid slice transition -/

open ProbLang

namespace SampLib.SliceTerms

theorem sliceStep_lc {rT : Type _} :
    (Occil.General.sliceStep : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem sliceStep_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.sliceStep = Occil.General.sliceStep :=
  (Exp.open_lc k e _ sliceStep_lc).symm

@[simp] theorem sliceStep_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.sliceStep : Exp rT) = Occil.General.sliceStep :=
  Exp.closeRec_fresh x _ k
    (by simp [Occil.General.sliceStep, Exp.fv, Rejection.rejection_fv,
      RndIntExcRange.rndIntExcRange_fv, Occil.uniformInt])

end SampLib.SliceTerms
