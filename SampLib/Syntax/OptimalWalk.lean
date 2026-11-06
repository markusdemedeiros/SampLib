import SampLib.Syntax.Optimal
import SampLib.Syntax.ListValues

/-! # A structural form of the cyclic walk's recursive closure -/

open ProbLang

namespace SampLib.Optimal.Program

private instance data_closed {rT : Type} [ProbLangℝ rT] (rows : List ℕ) :
    ClosedExp (listVal (fun m : ℕ => (Val.int m : Val rT)) rows).fst where
  lc := (listVal _ rows).lc
  fv := ListValues.listVal_fv _ rows (fun _ _ => rfl)

/-- Binder indices keep the captured matrix independent of quotation-closing wrappers. -/
def walkCode {rT : Type} (matrix : Exp rT) (k l : ℕ) (rejected : ℤ) : Exp rT :=
  let expanded := Exp.binop .plus (.binop .mult (.lit (.int 2)) (.bvar 1))
    (.rand (.lit (.int 2)) (.lit .unit))
  let scanColumn := Exp.app (.app (.app (.app scan matrix) (.bvar 0))
    (.binop .minus (.binop .minus (.lit (.int k)) (.lit (.int 1))) (.bvar 1))) (.lit (.int 0))
  let restart := Exp.app (.app (.bvar 4) (.lit (.int 0))) (.lit (.int 0))
  let nextColumn := Exp.cond (.binop .eq (.binop .plus (.bvar 2) (.lit (.int 1)))
    (.lit (.int k))) (.lit (.int l)) (.binop .plus (.bvar 2) (.lit (.int 1)))
  let advance := Exp.app (.app (.bvar 4) (.snd (.bvar 0))) nextColumn
  let select := Exp.cond (.fst (.bvar 0))
    (.cond (.binop .eq (.snd (.bvar 0)) (.lit (.int rejected))) restart (.snd (.bvar 0)))
    advance
  .fix (.lam (.lam (.app (.lam (.app (.lam select) scanColumn)) expanded)))

instance walkCode_closed {rT : Type} [ProbLangℝ rT] (rows : List ℕ) (k l : ℕ)
    (rejected : ℤ) :
    ClosedExp (walkCode (listVal (fun m : ℕ => (Val.int m : Val rT)) rows).fst k l rejected) where
  lc := by unfold walkCode; is_lc
  fv := by simp [walkCode, Exp.fv, ClosedExp.fv]

/-- The structural closure is the original source loop, with exactly the same captured data. -/
theorem walk_eq {rT : Type} [ProbLangℝ rT] (rows : List ℕ) (k l : ℕ) (rejected : ℤ) :
    walk (rT := rT) rows k l rejected =
      walkCode (listVal (fun m : ℕ => Val.int m) rows).fst k l rejected := by
  simp only [walk, walkCode, Exp.close, Exp.closeRec, ClosedExp.closeRec]
  congr 30

end SampLib.Optimal.Program
