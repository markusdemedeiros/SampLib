import SampLib.Weighted.Syntax.OptimalSource
import SampLib.Common.WeightedValidation

/-! # Closed canonical source constants for the weighted-choice wrapper -/

open ProbLang

namespace SampLib.Optimal.Program

instance matrix_closed {rT : Type} : ClosedExp (Occil.WeightedVariants.optimalMatrix : Exp rT) where
  lc := by rw [matrix_code_eq]; unfold matrixCode; is_lc
  fv := by
    rw [matrix_code_eq]
    simp [matrixCode, Exp.fv, ClosedExp.fv, WeightedValidation.validWeights_fv,
      WeightedValidation.sumInts_fv, length_fv]

instance draw_closed {rT : Type} : ClosedExp (Occil.WeightedVariants.optimalDraw : Exp rT) where
  lc := by rw [draw_code_eq]; unfold drawCode; is_lc
  fv := by
    rw [draw_code_eq]
    simp [drawCode, Exp.fv, ClosedExp.fv]

@[pl_fold] def choiceSource {rT : Type} : Exp rT :=
  dsimp% only [Occil.WeightedVariants.optimalChoice, Exp.close, Exp.closeRec]
    (Occil.WeightedVariants.optimalChoice : Exp rT)

theorem choice_source_eq {rT : Type} :
    (Occil.WeightedVariants.optimalChoice : Exp rT) = choiceSource := by kernel_rfl

end SampLib.Optimal.Program
