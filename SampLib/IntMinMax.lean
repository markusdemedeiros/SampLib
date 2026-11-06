import Metrology.TotalEris.WpTactics

/-! # Pure integer minimum and maximum conditionals -/

open ProbLang

namespace SampLib

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

/-- The conditional used by the source's integer minimum callback. -/
def intMinCond (a b : ℤ) : Exp rT :=
  .cond (.lit (.bool (decide (a < b)))) (.lit (.int a)) (.lit (.int b))

/-- The conditional used by the source's integer maximum callback. -/
def intMaxCond (a b : ℤ) : Exp rT :=
  .cond (.lit (.bool (decide (a < b)))) (.lit (.int b)) (.lit (.int a))

/-- An integer comparison selecting its smaller operand is a minimum. -/
instance (priority := 1100) pureExec_cond_intMin (a b : ℤ) :
    PureExec True 1
      (Exp.cond (.lit (.bool (decide (a < b)))) (.lit (.int a)) (.lit (.int b)) : Exp rT)
      (.lit (.int (min a b))) where
  pure_exec _ := by
    have hstep : PureStep
        (Exp.cond (.lit (.bool (decide (a < b)))) (.lit (.int a)) (.lit (.int b)) : Exp rT)
        (.lit (.int (min a b))) := by
      by_cases h : a < b
      · simpa only [decide_eq_true h, min_eq_left h.le] using
          (PureHeadStep.cond_true (pl(#int a) : Exp rT) pl(#int b)).toPureStep
      · simpa only [decide_eq_false h, min_eq_right (le_of_not_gt h)] using
          (PureHeadStep.cond_false (pl(#int a) : Exp rT) pl(#int b)).toPureStep
    exact ⟨_, hstep, rfl⟩

/-- An integer comparison selecting its larger operand is a maximum. -/
instance (priority := 1100) pureExec_cond_intMax (a b : ℤ) :
    PureExec True 1
      (Exp.cond (.lit (.bool (decide (a < b)))) (.lit (.int b)) (.lit (.int a)) : Exp rT)
      (.lit (.int (max a b))) where
  pure_exec _ := by
    have hstep : PureStep
        (Exp.cond (.lit (.bool (decide (a < b)))) (.lit (.int b)) (.lit (.int a)) : Exp rT)
        (.lit (.int (max a b))) := by
      by_cases h : a < b
      · simpa only [decide_eq_true h, max_eq_right h.le] using
          (PureHeadStep.cond_true (pl(#int b) : Exp rT) pl(#int a)).toPureStep
      · simpa only [decide_eq_false h, max_eq_left (le_of_not_gt h)] using
          (PureHeadStep.cond_false (pl(#int b) : Exp rT) pl(#int a)).toPureStep
    exact ⟨_, hstep, rfl⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Pure integer minimum, ready for a continuation under `twp_bind`. -/
theorem twp_intMin (E : CoPset) (a b : ℤ) (Φ : Val rT → IProp GF) :
    Φ (.int (min a b)) ⊢ tglWp E (intMinCond a b) Φ := by
  have : PureExec True 1 (intMinCond a b : Exp rT) pl(#int (min a b)) :=
    pureExec_cond_intMin a b
  have hstep : tglWp E pl(#int (min a b)) Φ ⊢ tglWp E (intMinCond a b) Φ := by
    simpa only [Ectx.fill, List.foldl_nil] using
      (twp_pure_step_ctx [] True (n := 1) (E := E) (Φ := Φ)
        (e₁ := intMinCond a b) (e₂ := pl(#int (min a b))) trivial)
  exact (tglWp_value (v := .int (min a b))).trans hstep

/-- Pure integer maximum, ready for a continuation under `twp_bind`. -/
theorem twp_intMax (E : CoPset) (a b : ℤ) (Φ : Val rT → IProp GF) :
    Φ (.int (max a b)) ⊢ tglWp E (intMaxCond a b) Φ := by
  have : PureExec True 1 (intMaxCond a b : Exp rT) pl(#int (max a b)) :=
    pureExec_cond_intMax a b
  have hstep : tglWp E pl(#int (max a b)) Φ ⊢ tglWp E (intMaxCond a b) Φ := by
    simpa only [Ectx.fill, List.foldl_nil] using
      (twp_pure_step_ctx [] True (n := 1) (E := E) (Φ := Φ)
        (e₁ := intMaxCond a b) (e₂ := pl(#int (max a b))) trivial)
  exact (tglWp_value (v := .int (max a b))).trans hstep

end specification

end

end SampLib
