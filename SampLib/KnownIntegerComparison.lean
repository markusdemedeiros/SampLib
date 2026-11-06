import SampLib.Templates

/-! # Integer comparisons with a known Boolean result

Supply the comparison fact directly, avoiding normalization of a large numeral
against an unknown integer in the pure-step tactic.
-/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.KnownIntegerComparison

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Execute one integer comparison using its already established result. -/
theorem twp_le (E : CoPset) (a b : ℤ) (result : Bool) (h : decide (a ≤ b) = result) :
    ⊢ tglWp E pl(#int a <= #int b) (fun v : Val rT => iprop(⌜v = Val.bool result⌝)) := by
  twp_pure_at pl(#int a <= #int b) ↦ pl(#bool result) by
    (by
      refine ⟨by is_value, by is_value, ?_⟩
      simp only [BinOp.eval, h])
  twp_value
  imodintro
  ipureintro
  rfl

/-- Execute integer equality using its already established result. -/
theorem twp_eq (E : CoPset) (a b : ℤ) (result : Bool) (h : (a == b) = result) :
    ⊢ tglWp E pl(#int a = #int b) (fun v : Val rT => iprop(⌜v = Val.bool result⌝)) := by
  twp_pure_at pl(#int a = #int b) ↦ pl(#bool result) by
    (by
      refine ⟨by is_value, by is_value, ?_⟩
      change (some (.lit (.bool (a == b))) : Option (Exp rT)) = some (.lit (.bool result))
      rw [h])
  twp_value
  imodintro
  ipureintro
  rfl

end SampLib.KnownIntegerComparison
