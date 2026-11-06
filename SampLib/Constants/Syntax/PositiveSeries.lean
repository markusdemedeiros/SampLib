import SampLib.Latent.UniformBagBracket
import Samplers.Constants.Engines

/-! # Structural source and binder interface for the positive-series engine

The source equality is kernel-checked before any callback is inserted.
Opening lemmas use only the callback value's local closure.
-/

open ProbLang

namespace SampLib.FromPositiveSeries.Program

/-- Structural binders keep the arbitrary callback as a locally closed value leaf. -/
def loopCode {rT : Type} (term : Exp rT) (bag : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (depth : ℕ) (x y : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (bag depth)) x) y
  let recur := .app (.app (.app (.bvar 13)
    (.binop .plus (.bvar 12) (.lit (.int 1)))) (.bvar 3)) (.bvar 2)
  let upper := bind (.binop .mult (.bvar 1) (.bvar 3))
    (.cond (compare 10 (.bvar 1) (.bvar 0)) recur (.lit (.bool false)))
  let upper := bind
    (.binop .plus (.binop .mult (.bvar 1) (.bvar 2)) (.binop .mult (.bvar 3) (.bvar 0)))
    upper
  let next := bind (.binop .mult (.bvar 7) (.bvar 4))
    (.cond (compare 8 (.bvar 1) (.bvar 0)) (.lit (.bool true)) upper)
  let next := bind
    (.binop .plus (.binop .mult (.bvar 7) (.bvar 3)) (.binop .mult (.bvar 4) (.bvar 6)))
    next
  let invalid := .binop .or
    (.binop .or
      (.binop .or (.binop .lt (.bvar 4) (.lit (.int 0)))
        (.binop .le (.bvar 3) (.lit (.int 0))))
      (.binop .lt (.bvar 1) (.lit (.int 0))))
    (.binop .le (.bvar 0) (.lit (.int 0)))
  let read := bind (.snd (.bvar 1)) (.cond invalid .fail next)
  let read := bind (.fst (.bvar 0)) read
  let read := bind (.snd (.snd (.bvar 2))) read
  let read := bind (.fst (.snd (.bvar 1))) read
  let read := bind (.fst (.bvar 0)) read
  let read := bind (.app term (.bvar 2)) read
  .fix (.lam (.lam (.lam read)))

def loop {rT : Type} (term : Val rT) (l : Loc) : Exp rT :=
  loopCode term.fst (fun _ => .lit (.loc l))

def sourceCode {rT : Type} : Exp rT :=
  let start := .app (.app (.app (.bvar 0) (.lit (.int 0))) (.lit (.int 0))) (.lit (.int 1))
  let decide := .app (.lam start) (loopCode (.bvar 6) (fun depth => .bvar (depth + 4)))
  .lam (.lam (.app (.lam decide) (.app Occil.newUniformBag (.lit .unit))))

theorem source_eq {rT : Type} :
    (Occil.Constants.fromPositiveSeries : Exp rT) = sourceCode := by
  kernel_rfl

theorem inserted_callback {rT : Type} (term : Val rT) :
    Exp.openRec 1 pl(#()) (Exp.openRec 2 term.fst
      (loopCode (.bvar 6) (fun depth => .bvar (depth + 4)))) =
      loopCode term.fst (fun depth => .bvar (depth + 4)) := by
  simp [loopCode, Exp.openRec, UniformBag.uniformBagLess_openRec,
    (Exp.open_lc 5 pl(#()) term.fst term.lc).symm]

def bagBody {rT : Type} (term : Val rT) : Exp rT :=
  let start := .app (.app (.app (.bvar 0) (.lit (.int 0))) (.lit (.int 0))) (.lit (.int 1))
  .app (.lam start) (loopCode term.fst (fun depth => .bvar (depth + 4)))

theorem opened_bag {rT : Type} (term : Val rT) (l : Loc) :
    Exp.open' (bagBody term) (Val.loc l).fst =
      pl(let decide := &(loop term l); decide #0 #0 #1) := by
  simp [bagBody, loop, loopCode, Exp.open', Exp.openRec,
    UniformBag.uniformBagLess_openRec,
    (Exp.open_lc 4 (Val.loc l).fst term.fst term.lc).symm]

theorem loop_locallyClosed {rT : Type} (term : Val rT) (l : Loc) :
    (loop term l).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have ht (k : ℕ) : Exp.lcb k term.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb term.lc) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.uniformBagLess : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb UniformBag.uniformBagLess_lc) (Nat.zero_le k)
  simp [loop, loopCode, Exp.lcb, ht, hu]

theorem bag_locallyClosed {rT : Type} (term : Val rT) :
    (Exp.lam (bagBody term)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have ht (k : ℕ) : Exp.lcb k term.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb term.lc) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.uniformBagLess : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb UniformBag.uniformBagLess_lc) (Nat.zero_le k)
  simp [bagBody, loopCode, Exp.lcb, ht, hu]

def sourceBody {rT : Type} : Exp rT :=
  let start := .app (.app (.app (.bvar 0) (.lit (.int 0))) (.lit (.int 0))) (.lit (.int 1))
  let decide := .app (.lam start) (loopCode (.bvar 6) (fun depth => .bvar (depth + 4)))
  .lam (.app (.lam decide) (.app Occil.newUniformBag (.lit .unit)))

theorem source_locallyClosed {rT : Type} :
    (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

theorem unit_locallyClosed {rT : Type} (term : Val rT) :
    (Exp.open' sourceBody term.fst).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb term.lc)
  change Exp.lcb 0 (sourceCode : Exp rT) = true
  exact Exp.lc_imp_lcb source_locallyClosed

end SampLib.FromPositiveSeries.Program
