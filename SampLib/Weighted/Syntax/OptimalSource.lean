import SampLib.Weighted.Syntax.OptimalTable

/-! # Structural source views for the cyclic preprocessing and direct draw

Explicit binders remove quotation-closing bookkeeping from symbolic execution.
Each view is checked against the canonical source by kernel conversion.
-/

open ProbLang

namespace SampLib.Optimal.Program

theorem bitLength_openRec {rT : Type} (i : ℕ) (e : Exp rT) :
    Exp.openRec i e Occil.WeightedVariants.bitLength = Occil.WeightedVariants.bitLength :=
  ClosedExp.openRec i e

theorem scan_openRec {rT : Type} (i : ℕ) (e : Exp rT) :
    Exp.openRec i e scan = scan := ClosedExp.openRec i e

theorem length_fv {rT : Type} : (Occil.length : Exp rT).fv = ∅ := by
  simp [Occil.length, Exp.fv]

theorem length_openRec {rT : Type} (i : ℕ) (e : Exp rT) :
    Exp.openRec i e Occil.length = Occil.length :=
  (Exp.open_lc i e _ (by is_lc)).symm

private def bind {rT : Type} (value body : Exp rT) : Exp rT := .app (.lam body) value
private def litInt {rT : Type} (n : ℤ) : Exp rT := .lit (.int n)
private def power {rT : Type} (exponent : Exp rT) : Exp rT :=
  .app (.app Occil.Weighted.integerPower (litInt 2)) exponent

/-- The search captures ceiling, width, and total after their three bindings. -/
private def selectSource {rT : Type} : Exp rT :=
  let retry := Exp.app (.app (.app (.bvar 4) (.binop .plus (.bvar 3) (litInt 1)))
    (.bvar 3)) (.bvar 0)
  let choose := Exp.cond (.binop .eq (.bvar 0) (.bvar 7)) (.pair (.bvar 3) (.bvar 0))
    (.cond (.binop .lt (.bvar 0) (.bvar 7)) (.pair (.bvar 2) (.bvar 1)) retry)
  let denominator := Exp.binop .minus (.bvar 4) (power (.bvar 2))
  .fix (.lam (.lam (.lam (.cond (.binop .le (.bvar 5) (.bvar 2))
    (.pair (.bvar 1) (.bvar 0)) (bind denominator choose)))))

private def appendSource {rT : Type} : Exp rT :=
  .fix (.lam (.case (.bvar 0) (.lam (.inr (.pair (.bvar 3) (.inl (.lit .unit)))))
    (.lam (.inr (.pair (.fst (.bvar 0)) (.app (.bvar 2) (.snd (.bvar 0))))))))

/-- The converter captures values, rejection numerator, denominator, prefix, and width. -/
private def encodeSource {rT : Type} : Exp rT :=
  let recurse := Exp.inr (.pair (.bvar 0) (.app (.bvar 5) (.snd (.bvar 3))))
  let divisor := Exp.binop .minus (.bvar 0) (litInt 1)
  let ordinary := Exp.binop .plus (.binop .mult (.binop .div (.bvar 1) divisor) (.bvar 0))
    (.binop .mod (.bvar 1) divisor)
  let encoded := Exp.cond (.binop .eq (.bvar 1) (.bvar 7)) (.binop .minus (.bvar 11) (litInt 1))
    (.cond (.binop .eq (.bvar 8) (.bvar 12)) (.bvar 1)
      (.cond (.binop .eq (.bvar 8) (litInt 0)) (.bvar 1) ordinary))
  let period := power (.binop .minus (.bvar 11) (.bvar 7))
  let nonempty := bind (.fst (.bvar 0)) (bind period (bind encoded recurse))
  .fix (.lam (.case (.bvar 0) (.lam (.inl (.lit .unit))) (.lam nonempty)))

@[pl_fold] def matrixSource {rT : Type} : Exp rT :=
  let result := Exp.pair (.app (.bvar 1) (.bvar 2))
    (.pair (.bvar 9) (.pair (.bvar 5) (.bvar 0)))
  let index := Exp.cond (.binop .eq (.bvar 2) (litInt 0)) (litInt (-1))
    (.app Occil.length (.bvar 10))
  let values := Exp.cond (.binop .eq (.bvar 0) (litInt 0)) (.bvar 8)
    (bind appendSource (.app (.bvar 0) (.bvar 9)))
  let selected := Exp.app (.app (.app (.bvar 0) (litInt 0)) (.bvar 2)) (.bvar 1)
  let finish := bind (.fst (.bvar 0)) (bind (.snd (.bvar 1))
    (bind (.binop .minus (.bvar 0) (.bvar 6))
      (bind values (bind encodeSource (bind index result)))))
  let afterTotal := bind (.app Occil.WeightedVariants.bitLength (.bvar 0))
    (bind (power (.bvar 0)) (bind selectSource (bind selected finish)))
  .lam (.cond (.app Occil.Weighted.validWeights (.bvar 0))
    (bind (.app Occil.sumInts (.bvar 0)) afterTotal) .fail)

theorem matrix_source_eq {rT : Type} :
    (Occil.WeightedVariants.optimalMatrix : Exp rT) = matrixSource := by kernel_rfl

@[pl_fold] def drawSourceCode {rT : Type} : Exp rT :=
  let expanded := Exp.binop .plus (.binop .mult (litInt 2) (.bvar 1))
    (.rand (litInt 2) (.lit .unit))
  let scanColumn := Exp.app (.app (.app (.app (.bvar 4) (.bvar 8)) (.bvar 0))
    (.binop .minus (.binop .minus (.bvar 7) (litInt 1)) (.bvar 1))) (litInt 0)
  let restart := Exp.app (.app (.bvar 4) (litInt 0)) (litInt 0)
  let nextColumn := Exp.cond (.binop .eq (.binop .plus (.bvar 2) (litInt 1)) (.bvar 8))
    (.bvar 7) (.binop .plus (.bvar 2) (litInt 1))
  let advance := Exp.app (.app (.bvar 4) (.snd (.bvar 0))) nextColumn
  let choose := Exp.cond (.fst (.bvar 0))
    (.cond (.binop .eq (.snd (.bvar 0)) (.bvar 6)) restart (.snd (.bvar 0))) advance
  let walk := Exp.fix (.lam (.lam (bind expanded (bind scanColumn choose))))
  let run := Exp.app (.app (.bvar 0) (litInt 0)) (litInt 0)
  .lam (.lam (bind (.fst (.bvar 1)) (bind (.fst (.snd (.bvar 2)))
    (bind (.fst (.snd (.snd (.bvar 3)))) (bind (.snd (.snd (.snd (.bvar 4))))
      (bind scan (bind walk run)))))))

theorem draw_sourceCode_eq {rT : Type} :
    (Occil.WeightedVariants.optimalDraw : Exp rT) = drawSourceCode := by kernel_rfl

/-- Expand captured-index staging fragments before the LC tactics inspect the whole closure. -/
@[pl_fold] def matrixCode {rT : Type} : Exp rT :=
  dsimp% only [matrixSource, bind, litInt, power, selectSource, appendSource, encodeSource]
    (matrixSource : Exp rT)

theorem matrix_code_eq {rT : Type} :
    (Occil.WeightedVariants.optimalMatrix : Exp rT) = matrixCode := by kernel_rfl

@[pl_fold] def drawCode {rT : Type} : Exp rT :=
  dsimp% only [drawSourceCode, bind, litInt] (drawSourceCode : Exp rT)

theorem draw_code_eq {rT : Type} :
    (Occil.WeightedVariants.optimalDraw : Exp rT) = drawCode := by kernel_rfl

end SampLib.Optimal.Program
