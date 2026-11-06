import SampLib.Weighted.Syntax.KnuthYao
import SampLib.Weighted.Support.PowerOfTwoCeiling

/-! # Checked source fragments for the fast loaded dice roller -/

open ProbLang

namespace SampLib.FastLoadedDice.Program

/-- The enclosing bindings are supplied at their current binder depth. -/
def scanCode {rT : Type} (draw place padded total : ℕ → Exp rT) : Exp rT :=
  let dummy := Exp.binop .mod
    (.binop .div (.binop .minus (padded 5) (total 5)) (place 5)) (.lit (.int 2))
  let restart := Exp.app (.app (draw 6) (.binop .div (padded 6) (.lit (.int 2))))
    (.lit (.int 0))
  let advance := Exp.app (.app (draw 6) (.binop .div (place 6) (.lit (.int 2))))
    (.binop .minus (.bvar 3) (.bvar 0))
  let nilCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) restart advance)) dummy
  let bit := Exp.binop .mod (.binop .div (.fst (.bvar 0)) (place 5)) (.lit (.int 2))
  let recur := Exp.app (.app (.app (.bvar 5) (.snd (.bvar 1)))
    (.binop .minus (.bvar 3) (.bvar 0))) (.binop .plus (.bvar 2) (.lit (.int 1)))
  let consCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) (.bvar 2) recur)) bit
  .fix (.lam (.lam (.lam (.case (.bvar 2) (.lam nilCase) (.lam consCase)))))

def loopCode {rT : Type} (weights padded total : ℕ → Exp rT) : Exp rT :=
  let next := Exp.binop .plus (.binop .mult (.bvar 0) (.lit (.int 2)))
    (.rand (.lit (.int 2)) (.lit .unit))
  let dummy := Exp.binop .mod
    (.binop .div (.binop .minus (padded 9) (total 9)) (.bvar 7)) (.lit (.int 2))
  let restart := Exp.app (.app (.bvar 9) (.binop .div (padded 10) (.lit (.int 2))))
    (.lit (.int 0))
  let advance := Exp.app (.app (.bvar 9) (.binop .div (.bvar 8) (.lit (.int 2))))
    (.binop .minus (.bvar 3) (.bvar 0))
  let nilCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) restart advance)) dummy
  let bit := Exp.binop .mod (.binop .div (.fst (.bvar 0)) (.bvar 7)) (.lit (.int 2))
  let recur := Exp.app (.app (.app (.bvar 5) (.snd (.bvar 1)))
    (.binop .minus (.bvar 3) (.bvar 0))) (.binop .plus (.bvar 2) (.lit (.int 1)))
  let consCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) (.bvar 2) recur)) bit
  let scan := Exp.fix (.lam (.lam (.lam (.case (.bvar 2) (.lam nilCase) (.lam consCase)))))
  let run := Exp.app (.app (.app (.bvar 0) (weights 5)) (.bvar 1)) (.lit (.int 0))
  let body := Exp.cond (.binop .le (.bvar 3) (.lit (.int 0))) .fail run
  .fix (.lam (.lam (.app (.lam (.app (.lam body) scan)) next)))

@[pl_fold] def loop {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (P T : ℕ) : Exp rT :=
  loopCode (fun _ => (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst)
    (fun _ => .lit (.int P)) (fun _ => .lit (.int T))

@[pl_fold] def scan {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (P T place : ℕ) : Exp rT :=
  scanCode (fun _ => loop ws P T) (fun _ => .lit (.int place))
    (fun _ => .lit (.int P)) (fun _ => .lit (.int T))

instance loop_closed {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (P T : ℕ) :
    ClosedExp (loop (rT := rT) ws P T) where
  lc := by unfold loop loopCode; is_lc
  fv := by simp [loop, loopCode, Exp.fv, ClosedExp.fv]

theorem scan_lc {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (P T place : ℕ) :
    (scan (rT := rT) ws P T place).IsLocallyClosed := by
  unfold scan scanCode loop loopCode
  is_lc

def scanValue {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (P T place : ℕ) : Val rT :=
  ⟨scan ws P T place, .fix (scan_lc ws P T place), scan_lc ws P T place⟩

private def afterBitBody {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (place : ℕ) (scanner : Exp rT) : Exp rT :=
  let run := Exp.app (.app (.app (.bvar 0)
    (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst) (.bvar 1)) (.lit (.int 0))
  .lam (.app (.lam (.cond (.binop .le (.lit (.int place)) (.lit (.int 0))) .fail run)) scanner)

def afterRandClosed {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (P T place rank : ℕ) (bit : ℤ) : Exp rT :=
  let next := Exp.binop .plus (.binop .mult (.lit (.int rank)) (.lit (.int 2))) (.lit (.int bit))
  .app (afterBitBody ws place (scanValue ws P T place).fst) next

def afterBit {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (P T place next : ℕ) : Exp rT :=
  .app (afterBitBody ws place (scanValue ws P T place).fst) (.lit (.int next))

@[pl_fold] def afterPadding {rT : Type} [ProbLangℝ rT]
    (ws : List ℕ) (P T : ℕ) : Exp rT :=
  let weights := (listVal (fun w : ℕ => (Val.int w : Val rT)) ws).fst
  let run := Exp.app (.app (.bvar 0) (.binop .div (.lit (.int P)) (.lit (.int 2))))
    (.lit (.int 0))
  let choose := Exp.cond (.binop .le (.lit (.int 0)) (.bvar 0)) (.bvar 0)
    (.app (.lam run) (loop ws P T))
  let search := Exp.app (.app (.bvar 0) weights) (.lit (.int 0))
  .app (.lam (.app (.lam choose) search)) (KnuthYao.Program.find T)

def sourceCode {rT : Type} : Exp rT :=
  let dummy := Exp.binop .mod
    (.binop .div (.binop .minus (.bvar 11) (.bvar 12)) (.bvar 7)) (.lit (.int 2))
  let restart := Exp.app (.app (.bvar 9) (.binop .div (.bvar 12) (.lit (.int 2))))
    (.lit (.int 0))
  let advance := Exp.app (.app (.bvar 9) (.binop .div (.bvar 8) (.lit (.int 2))))
    (.binop .minus (.bvar 3) (.bvar 0))
  let nilCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) restart advance)) dummy
  let bit := Exp.binop .mod (.binop .div (.fst (.bvar 0)) (.bvar 7)) (.lit (.int 2))
  let recur := Exp.app (.app (.app (.bvar 5) (.snd (.bvar 1)))
    (.binop .minus (.bvar 3) (.bvar 0))) (.binop .plus (.bvar 2) (.lit (.int 1)))
  let consCase := Exp.app (.lam (.cond (.binop .lt (.bvar 3) (.bvar 0)) (.bvar 2) recur)) bit
  let scan := Exp.fix (.lam (.lam (.lam (.case (.bvar 2) (.lam nilCase) (.lam consCase)))))
  let next := Exp.binop .plus (.binop .mult (.bvar 0) (.lit (.int 2)))
    (.rand (.lit (.int 2)) (.lit .unit))
  let scanRun := Exp.app (.app (.app (.bvar 0) (.bvar 10)) (.bvar 1)) (.lit (.int 0))
  let body := Exp.cond (.binop .le (.bvar 3) (.lit (.int 0))) .fail scanRun
  let draw := Exp.fix (.lam (.lam (.app (.lam (.app (.lam body) scan)) next)))
  let run := Exp.app (.app (.bvar 0) (.binop .div (.bvar 3) (.lit (.int 2)))) (.lit (.int 0))
  let choose := Exp.cond (.binop .le (.lit (.int 0)) (.bvar 0)) (.bvar 0)
    (.app (.lam run) draw)
  let search := Exp.app (.app (.bvar 0) (.bvar 4)) (.lit (.int 0))
  let findRetry := Exp.app (.app (.bvar 3) (.snd (.bvar 0)))
    (.binop .plus (.bvar 1) (.lit (.int 1)))
  let findBody := Exp.case (.bvar 1) (.lam (.lit (.int (-1))))
    (.lam (.cond (.binop .eq (.fst (.bvar 0)) (.bvar 5)) (.bvar 1) findRetry))
  let finder := Exp.fix (.lam (.lam findBody))
  let afterPadding := Exp.app (.lam (.app (.lam choose) search)) finder
  let afterTotal := Exp.app (.lam afterPadding)
    (.app Occil.Weighted.powerOfTwoCeiling (.bvar 0))
  .lam (.lam (.cond (.app Occil.Weighted.validWeights (.bvar 1))
    (.app (.lam afterTotal) (.app Occil.sumInts (.bvar 1))) .fail))

theorem source_eq {rT : Type} :
    (Occil.Weighted.fastLoadedDiceRoller : Exp rT) = sourceCode := by kernel_rfl

def source {rT : Type} : Val rT := ⟨sourceCode, .lam (by is_lc), by is_lc⟩

theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.Weighted.fastLoadedDiceRoller := source_eq.symm

end SampLib.FastLoadedDice.Program
