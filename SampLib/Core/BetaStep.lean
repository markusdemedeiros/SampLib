import Metrology.TotalEris.WpTactics

/-! # A beta step retaining the named lambda body -/

open ProbLang Iris Iris.BI TotalEris ErisWpGS

namespace SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-- Apply beta reduction without normalizing the opened body. -/
theorem twp_beta (E : CoPset) (K : Ectx rT) (body : Exp rT) (v : Val rT)
    (hc : (Exp.lam body).IsLocallyClosed) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (Exp.open' body v.fst)) Φ ⊢
      tglWp E (K.fill (.app (.lam body) v.fst)) Φ :=
  twp_pure_step_ctx K (v.fst.isValue ∧ (Exp.lam body).IsLocallyClosed) ⟨⟨v.snd⟩, hc⟩

end SampLib
