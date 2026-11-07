import SampLib.PSRN.Syntax.PSRNExponential

/-! # Cached deterministic steps for the decay-based exponential constructor -/

open ProbLang Iris Iris.BI TotalEris ErisWpGS

namespace SampLib.PSRNExponential.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

theorem twp_open (E : CoPset) (decay : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (body decay) Φ ⊢
      tglWp E pl(&Occil.PSRN.newExponentialFromDecay &decay.fst #()) Φ := by
  have h := CurriedStep.twp_apply E [] [decay, .unit] sourceBody
    (sourceBody_lcb (rT := rT)) Φ
  rw [opened_source] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil, Ectx.fill,
    List.foldl_cons, List.foldl_nil,
    Function.flip_def, EctxItem.fillItem, Exp.ofVal] using h

theorem twp_afterCount (E : CoPset) (decay : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (countBody decay) Φ ⊢ tglWp E (body decay) Φ := by
  have h := twp_beta E [] (afterCount decay) (ExponentialCount.Program.countVal decay)
    (afterCount_lc decay) Φ
  rw [opened_afterCount] at h
  simpa only [Ectx.fill_nil, body, bind] using h

theorem twp_afterWhole (E : CoPset) (decay : Val rT) (whole : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (wholeBody decay whole) Φ ⊢
      tglWp E (.app (.lam (afterWhole decay)) (.lit (.int whole))) Φ := by
  have h := twp_beta E [] (afterWhole decay) (.int whole) (afterWhole_lc decay) Φ
  rw [opened_afterWhole] at h
  simpa only [Ectx.fill_nil] using h

theorem twp_afterDigits (E : CoPset) (whole : ℤ) (value : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.add (&Occil.PSRN.rational #whole #1) &value.fst) Φ ⊢
      tglWp E (.app (.lam (afterDigits whole)) value.fst) Φ := by
  have h := twp_beta E [] (afterDigits whole) value (afterDigits_lc whole) Φ
  rw [opened_afterDigits] at h
  simpa only [Ectx.fill_nil] using h

end SampLib.PSRNExponential.Program
