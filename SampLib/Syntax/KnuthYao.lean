import SampLib.Syntax.ClosedExp
import SampLib.Syntax.ListValues
import Samplers.Weighted.Trees

/-! # Closed source fragments for Knuth–Yao's actual matrix walk -/

open ProbLang

namespace SampLib.KnuthYao.Program

private instance data_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    ClosedExp (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst where
  lc := (listVal _ ws).lc
  fv := ListValues.listVal_fv _ ws (fun _ _ => rfl)

instance matrixColumn_closed {rT : Type} :
    ClosedExp (Occil.Weighted.matrixColumn : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Weighted.matrixColumn, Exp.fv, Exp.close, Exp.closeRec]

@[pl_fold] def loop {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (T : ℕ) : Exp rT := pl%
  rec draw multiplier distance :=
    let next := distance * #2 + rand(#2, #());
    case! (&Occil.Weighted.matrixColumn
        &(listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst multiplier #int (T : ℤ) next #0)
      | inl(label) => label
      | inr(rest) => draw (multiplier * #2) rest

/-- Structural form keeps the recursive closure independent of quotation closing wrappers. -/
def loopCode {rT : Type} (weights : Exp rT) (T : ℕ) : Exp rT :=
  let next := Exp.binop .plus (.binop .mult (.bvar 0) (.lit (.int 2)))
    (.rand (.lit (.int 2)) (.lit .unit))
  let scan := Exp.app (.app (.app (.app (.app Occil.Weighted.matrixColumn weights)
    (.bvar 2)) (.lit (.int T))) (.bvar 0)) (.lit (.int 0))
  let retry := Exp.app (.app (.bvar 4) (.binop .mult (.bvar 3) (.lit (.int 2)))) (.bvar 0)
  .fix (.lam (.lam (.app (.lam (.case scan (.lam (.bvar 0)) (.lam retry))) next)))

instance loopCode_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (T : ℕ) :
    ClosedExp (loopCode (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst T) where
  lc := by unfold loopCode; is_lc
  fv := by simp [loopCode, Exp.fv, ClosedExp.fv]

theorem loop_eq {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (T : ℕ) :
    loop (rT := rT) ws T = loopCode (listVal (fun w : ℕ => Val.int w) ws).fst T := by
  simp only [loop, loopCode, Exp.close, Exp.closeRec, ClosedExp.closeRec]
  congr 20

@[pl_fold] def find {rT : Type} [ProbLangℝ rT] (T : ℕ) : Exp rT := pl%
  rec search xs i := case! xs
    | inl(u) => #(-1)
    | inr(p) => if fst(p) = #int (T : ℤ) then i else search (snd(p)) (i + #1)

@[pl_fold] def afterTotal {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (T : ℕ) : Exp rT :=
  let weights := (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst
  let run := Exp.app (.app (.bvar 0) (.lit (.int 2))) (.lit (.int 0))
  let choose := Exp.cond (.binop .le (.lit (.int 0)) (.bvar 0)) (.bvar 0)
    (.app (.lam run) (loopCode weights T))
  let search := Exp.app (.app (.bvar 0) weights) (.lit (.int 0))
  .app (.lam (.app (.lam choose) search)) (find T)

/-- Closed original source, before substituting caller data beneath its binders. -/
def sourceCode {rT : Type} : Exp rT :=
  let findRetry := Exp.app (.app (.bvar 3) (.snd (.bvar 0)))
    (.binop .plus (.bvar 1) (.lit (.int 1)))
  let findBody := Exp.case (.bvar 1) (.lam (.lit (.int (-1))))
    (.lam (.cond (.binop .eq (.fst (.bvar 0)) (.bvar 4)) (.bvar 1) findRetry))
  let finder := Exp.fix (.lam (.lam findBody))
  let next := Exp.binop .plus (.binop .mult (.bvar 0) (.lit (.int 2)))
    (.rand (.lit (.int 2)) (.lit .unit))
  let scan := Exp.app (.app (.app (.app (.app Occil.Weighted.matrixColumn (.bvar 8))
    (.bvar 2)) (.bvar 6)) (.bvar 0)) (.lit (.int 0))
  let retry := Exp.app (.app (.bvar 4) (.binop .mult (.bvar 3) (.lit (.int 2)))) (.bvar 0)
  let draw := Exp.fix (.lam (.lam (.app (.lam (.case scan (.lam (.bvar 0)) (.lam retry))) next)))
  let run := Exp.app (.app (.bvar 0) (.lit (.int 2))) (.lit (.int 0))
  let choose := Exp.cond (.binop .le (.lit (.int 0)) (.bvar 0)) (.bvar 0)
    (.app (.lam run) draw)
  let search := Exp.app (.app (.bvar 0) (.bvar 3)) (.lit (.int 0))
  let afterSum := Exp.app (.lam (.app (.lam choose) search)) finder
  .lam (.lam (.cond (.app Occil.Weighted.validWeights (.bvar 1))
    (.app (.lam afterSum) (.app Occil.sumInts (.bvar 1))) .fail))

theorem source_eq {rT : Type} : (Occil.Weighted.knuthYao : Exp rT) = sourceCode := by
  kernel_rfl

def source {rT : Type} : Val rT := ⟨sourceCode, .lam (by is_lc), by is_lc⟩

theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.Weighted.knuthYao := source_eq.symm

end SampLib.KnuthYao.Program
