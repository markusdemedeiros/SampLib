import SampLib.PSRN.Syntax.PSRNExponentialWrappers

/-! # Cached deterministic entry steps for the exponential rate wrappers -/

open ProbLang Iris Iris.BI TotalEris ErisWpGS

namespace SampLib.PSRNExponential.Wrappers

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

theorem twp_rational_open (E : CoPset) (a b : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (rationalBody a b) Φ ⊢
      tglWp E pl(&Occil.PSRN.newExponential #a #b #()) Φ := by
  have h := CurriedStep.twp_apply E [] [.int a, .int b, .unit] rationalSource
    (rational_lcb (rT := rT)) Φ
  rw [rational_opened] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← rational_source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem,
    Exp.ofVal] using h

theorem twp_log_open (E : CoPset) (x y : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (logBody x y) Φ ⊢
      tglWp E pl(&Occil.PSRN.newExponentialLogRate #x #y #()) Φ := by
  have h := CurriedStep.twp_apply E [] [.int x, .int y, .unit] logSource
    (log_lcb (rT := rT)) Φ
  rw [log_opened] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← log_source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem,
    Exp.ofVal] using h

theorem twp_unknown_open (E : CoPset) (coin : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (unknownBody coin) Φ ⊢
      tglWp E pl(&Occil.PSRN.newExponentialUnknownRate &coin.fst #()) Φ := by
  have h := CurriedStep.twp_apply E [] [coin, .unit] unknownSource
    (unknown_lcb (rT := rT)) Φ
  rw [unknown_opened] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← unknown_source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem,
    Exp.ofVal] using h

end SampLib.PSRNExponential.Wrappers
