import SampLib.Core.BetaStep

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

-- The argument is arbitrary, including locally closed values with named free variables.
example (E : CoPset) (v : Val rT) (R : IProp GF) (Φ : Val rT → IProp GF) :
    R ∗ Φ v ⊢ tglWp E (.app (.lam (.bvar 0)) v.fst) (fun w => iprop(R ∗ Φ w)) := by
  have h := SampLib.twp_beta E [] (.bvar 0) v (by is_lc) (fun w => iprop(R ∗ Φ w))
  simp only [Ectx.fill, List.foldl_nil] at h
  iintro H
  iapply h
  isimp only [Exp.open', Exp.openRec, ite_true]
  iapply (tglWp_value_of_toVal (E := E) (Φ := fun w => iprop(R ∗ Φ w))
    (Val.toVal?_fst v)) $$ H

#print axioms SampLib.twp_beta
