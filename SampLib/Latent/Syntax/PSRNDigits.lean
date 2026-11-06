import SampLib.Core.Syntax.ClosedExp
import Samplers.PSRN.Uniform

/-! # Source transport for conditional digit streams

Callbacks are inserted after closing every static binder. Their free variables
are retained, including names used internally by the ProbLang quotation syntax.
-/

open ProbLang

namespace SampLib.LatentDigits.Syntax

scoped instance bag_closed {rT : Type} : ClosedExp (Occil.newUniformBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.newUniformBag, Exp.fv]

theorem open_value {rT : Type} (k : ℕ) (e : Exp rT) (v : Val rT) :
    Exp.openRec k e v.fst = v.fst := (Exp.open_lc k e v.fst v.lc).symm

def bind {rT : Type} (e body : Exp rT) : Exp rT := .app (.lam body) e

theorem bind_fv {rT : Type} (e body : Exp rT) :
    (bind e body).fv = body.fv ∪ e.fv := rfl

/-- The exact recursive reader, with its callback inserted outside binder closure. -/
def readCode {rT : Type} (nextBit : Exp rT) : Exp rT :=
  let fresh := bind (.app Occil.newUniformBag (.lit .unit))
    (bind (.app (.app nextBit (.bvar 4)) (.bvar 3))
      (bind (.pair (.bvar 0) (.bvar 1))
        (bind (.store (.bvar 8) (.inr (.bvar 0))) (.bvar 1))))
  let step := .case (.bvar 0) (.lam fresh) (.lam (.bvar 0))
  let recur := .app (.app (.app (.app (.bvar 7) (.snd (.bvar 1)))
    (.binop .minus (.bvar 5) (.lit (.int 1))))
    (.binop .plus (.binop .mult (.bvar 4) (.lit (.int 2))) (.bvar 0)))
    (.binop .mult (.bvar 3) (.lit (.int 2)))
  let advance := bind (.load (.bvar 3))
    (bind step (bind (.cond (.fst (.bvar 0)) (.lit (.int 1)) (.lit (.int 0))) recur))
  .fix (.lam (.lam (.lam (.lam
    (.cond (.binop .eq (.bvar 2) (.lit (.int 0)))
      (.pair (.bvar 1) (.pair (.binop .plus (.bvar 1) (.lit (.int 1))) (.bvar 0)))
      advance)))))

/-- Four arguments are node, remaining digits, prefix numerator, and denominator. -/
def readVal {rT : Type} (nextBit : Val rT) : Val rT := by
  have hc (k : ℕ) : Exp.lcb k nextBit.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb nextBit.lc) (Nat.zero_le k)
  have hb (k : ℕ) : Exp.lcb k (Occil.newUniformBag : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (bag_closed (rT := rT)).lc) (Nat.zero_le k)
  refine ⟨readCode nextBit.fst, .fix ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [readCode, bind, Exp.lcb, hc, hb]

def oracleCode {rT : Type} (nextBit : Val rT) (root : Loc) : Exp rT :=
  .lam (.cond (.binop .lt (.bvar 0) (.lit (.int 0))) .fail
    (bind (readVal nextBit).fst
      (.app (.app (.app (.app (.bvar 0) (.lit (.loc root))) (.bvar 1))
        (.lit (.int 0))) (.lit (.int 1)))))

/-- Every observation starts at the same allocated root. -/
def oracleVal {rT : Type} (nextBit : Val rT) (root : Loc) : Val rT := by
  have hr (k : ℕ) : Exp.lcb k (readVal nextBit).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (readVal nextBit).lc) (Nat.zero_le k)
  refine ⟨oracleCode nextBit root, .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [oracleCode, bind, Exp.lcb, hr]

def oracleBody {rT : Type} (nextBit : Val rT) (root : Loc) : Exp rT :=
  match oracleCode nextBit root with
  | .lam body => body
  | _ => .lit .unit

def readCallBody {rT : Type} (root : Loc) (precision : ℕ) : Exp rT :=
  .app (.app (.app (.app (.bvar 0) (.lit (.loc root)))
    (.lit (.int (precision : ℤ)))) (.lit (.int 0))) (.lit (.int 1))

theorem oracle_open {rT : Type} (nextBit : Val rT) (root : Loc) (precision : ℕ) :
    Exp.open' (oracleBody nextBit root) (.lit (.int (precision : ℤ))) =
      .cond (.binop .lt (.lit (.int (precision : ℤ))) (.lit (.int 0))) .fail
        (bind (readVal nextBit).fst (readCallBody root precision)) := by
  simp [oracleBody, oracleCode, readCallBody, bind, Exp.open', Exp.openRec, open_value]

/-- The allocation body after applying the original constructor to its two arguments. -/
def constructorBody {rT : Type} : Exp rT :=
  match (Occil.PSRN.newByDigits : Exp rT) with
  | .lam (.lam body) => body
  | _ => .lit .unit

scoped instance constructor_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newByDigits : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.PSRN.newByDigits, Occil.newUniformBag, Exp.fv]

/-- Cached outer constructor value. -/
def sourceVal {rT : Type} : Val rT :=
  ⟨.lam (.lam constructorBody), .lam (constructor_closed (rT := rT)).lc,
    (constructor_closed (rT := rT)).lc⟩

theorem source_fst {rT : Type} : (sourceVal (rT := rT)).fst = Occil.PSRN.newByDigits := rfl

def partialBody {rT : Type} (nextBit : Val rT) : Exp rT :=
  Exp.openRec 1 nextBit.fst constructorBody

private theorem constructorBody_lcb {rT : Type} :
    Exp.lcb 2 (constructorBody (rT := rT)) = true := by lcb_decide

/-- Cached constructor after capturing its callback. -/
def partialVal {rT : Type} (nextBit : Val rT) : Val rT := by
  have hc : Exp.lcb 1 (partialBody nextBit) = true :=
    Exp.lcb_openRec (Exp.lcb_mono (Exp.lc_imp_lcb nextBit.lc) (by decide : 0 ≤ 1))
      (constructorBody_lcb (rT := rT))
  exact ⟨.lam (partialBody nextBit), .lam (Exp.lcb_imp_lc hc), Exp.lcb_imp_lc hc⟩

theorem source_beta {rT : Type} (nextBit : Val rT) :
    Exp.open' (.lam constructorBody) nextBit.fst = (partialVal nextBit).fst := rfl

/-- Its root binder, before the newly allocated location is substituted. -/
def oracleTemplate {rT : Type} : Exp rT :=
  match (constructorBody : Exp rT) with
  | .app (.lam body) _ => body
  | _ => .lit .unit

/-- After the two constructor beta steps, only the fresh root allocation remains. -/
theorem constructor_opened {rT : Type} (nextBit : Val rT) :
    Exp.open' (partialBody nextBit) (.lit .unit) =
      .app (.lam (Exp.openRec 1 (.lit .unit) (Exp.openRec 2 nextBit.fst oracleTemplate)))
        (.app Occil.newUniformBag (.lit .unit)) := by
  simp [partialBody, constructorBody, oracleTemplate, Occil.PSRN.newByDigits,
    Exp.open', Exp.openRec, Exp.close, Exp.closeRec, ClosedExp.openRec,
    ClosedExp.closeRec, Var.internal.injEq, open_value]

def rootBody {rT : Type} (nextBit : Val rT) : Exp rT :=
  Exp.openRec 1 (.lit .unit) (Exp.openRec 2 nextBit.fst oracleTemplate)

private theorem oracleTemplate_lcb {rT : Type} :
    Exp.lcb 3 (oracleTemplate (rT := rT)) = true := by lcb_decide

private theorem rootBody_lcb {rT : Type} (nextBit : Val rT) :
    Exp.lcb 1 (rootBody nextBit) = true :=
  Exp.lcb_openRec (by simp [Exp.lcb])
    (Exp.lcb_openRec
      (Exp.lcb_mono (Exp.lc_imp_lcb nextBit.lc) (by decide : 0 ≤ 2))
      (oracleTemplate_lcb (rT := rT)))

/-- Cached closure receiving the newly allocated root location. -/
def rootBinderVal {rT : Type} (nextBit : Val rT) : Val rT :=
  ⟨.lam (rootBody nextBit), .lam (Exp.lcb_imp_lc (rootBody_lcb nextBit)),
    Exp.lcb_imp_lc (rootBody_lcb nextBit)⟩

/-- The original constructor returns exactly the named oracle after allocating its root. -/
theorem allocated_oracle {rT : Type} (nextBit : Val rT) (root : Loc) :
    Exp.open' (Exp.openRec 1 (.lit .unit)
      (Exp.openRec 2 nextBit.fst oracleTemplate)) (.lit (.loc root)) =
      (oracleVal nextBit root).fst := by
  simp [oracleTemplate, constructorBody, Occil.PSRN.newByDigits, oracleVal, oracleCode,
    readVal, readCode, bind, Exp.open', Exp.openRec, Exp.close, Exp.closeRec,
    ClosedExp.openRec, ClosedExp.closeRec, Var.internal.injEq, open_value]

/-- The branch body beneath the reader's fixpoint and four argument binders. -/
def loopTemplate {rT : Type} (nextBit : Val rT) : Exp rT :=
  match readCode nextBit.fst with
  | .fix (.lam (.lam (.lam (.lam body)))) => body
  | _ => .lit .unit

/-- Fresh-case body: allocate the tail before calling the conditional digit sampler. -/
def fresh {rT : Type} (nextBit : Val rT) (node : Loc)
    (numerator denominator : ℤ) : Exp rT :=
  bind (.app Occil.newUniformBag (.lit .unit))
    (bind (.app (.app nextBit.fst (.lit (.int numerator))) (.lit (.int denominator)))
      (bind (.pair (.bvar 0) (.bvar 1))
        (bind (.store (.lit (.loc node)) (.inr (.bvar 0))) (.bvar 1))))

theorem fresh_lc {rT : Type} (nextBit : Val rT) (node : Loc)
    (numerator denominator : ℤ) : (fresh nextBit node numerator denominator).IsLocallyClosed := by
  have hc (k : ℕ) : Exp.lcb k nextBit.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb nextBit.lc) (Nat.zero_le k)
  have hb (k : ℕ) : Exp.lcb k (Occil.newUniformBag : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (bag_closed (rT := rT)).lc) (Nat.zero_le k)
  apply Exp.lcb_imp_lc
  simp [fresh, bind, Exp.lcb, hc, hb]

theorem fresh_open {rT : Type} (nextBit : Val rT) (node : Loc)
    (numerator denominator : ℤ) (k : ℕ) (v : Exp rT) :
    Exp.openRec k v (fresh nextBit node numerator denominator) =
      fresh nextBit node numerator denominator :=
  (Exp.open_lc _ _ _ (fresh_lc nextBit node numerator denominator)).symm

/-- The actual load/conditional callback/store sequence at the current node. -/
def step {rT : Type} (nextBit : Val rT) (node : Loc) (numerator denominator : ℤ) : Exp rT :=
  let fresh := bind (.app Occil.newUniformBag (.lit .unit))
    (bind (.app (.app nextBit.fst (.lit (.int numerator))) (.lit (.int denominator)))
      (bind (.pair (.bvar 0) (.bvar 1))
        (bind (.store (.lit (.loc node)) (.inr (.bvar 0))) (.bvar 1))))
  bind (.load (.lit (.loc node)))
    (.case (.bvar 0) (.lam fresh) (.lam (.bvar 0)))

/-- One opened branch body, retaining the source's original let nesting. -/
def openedReadCode {rT : Type} (nextBit : Val rT) (node : Loc)
    (remaining numerator denominator : ℤ) : Exp rT :=
  let fresh := bind (.app Occil.newUniformBag (.lit .unit))
    (bind (.app (.app nextBit.fst (.lit (.int numerator))) (.lit (.int denominator)))
      (bind (.pair (.bvar 0) (.bvar 1))
        (bind (.store (.lit (.loc node)) (.inr (.bvar 0))) (.bvar 1))))
  let step := .case (.bvar 0) (.lam fresh) (.lam (.bvar 0))
  let recur := .app (.app (.app (.app (readVal nextBit).fst (.snd (.bvar 1)))
    (.binop .minus (.lit (.int remaining)) (.lit (.int 1))))
    (.binop .plus (.binop .mult (.lit (.int numerator)) (.lit (.int 2))) (.bvar 0)))
    (.binop .mult (.lit (.int denominator)) (.lit (.int 2)))
  .cond (.binop .eq (.lit (.int remaining)) (.lit (.int 0)))
    (.pair (.lit (.int numerator))
      (.pair (.binop .plus (.lit (.int numerator)) (.lit (.int 1))) (.lit (.int denominator))))
    (bind (.load (.lit (.loc node)))
      (bind step (bind (.cond (.fst (.bvar 0)) (.lit (.int 1)) (.lit (.int 0))) recur)))

/-- After fix unfolding and four beta steps, no callback substitution remains. -/
theorem read_apply {rT : Type} (nextBit : Val rT) (node : Loc)
    (remaining numerator denominator : ℤ) :
    Exp.openRec 0 (.lit (.int denominator))
      (Exp.openRec 1 (.lit (.int numerator))
        (Exp.openRec 2 (.lit (.int remaining))
          (Exp.openRec 3 (.lit (.loc node))
            (Exp.openRec 4 (readVal nextBit).fst (loopTemplate nextBit))))) =
      openedReadCode nextBit node remaining numerator denominator := by
  simp [loopTemplate, readCode, openedReadCode, bind, Exp.openRec,
    open_value, ClosedExp.openRec]

private theorem loop_lcb {rT : Type} (nextBit : Val rT) :
    Exp.lcb 5 (loopTemplate nextBit) = true := by
  have hc (k : ℕ) : Exp.lcb k nextBit.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb nextBit.lc) (Nat.zero_le k)
  have hb (k : ℕ) : Exp.lcb k (Occil.newUniformBag : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (bag_closed (rT := rT)).lc) (Nat.zero_le k)
  simp [loopTemplate, readCode, bind, Exp.lcb, hc, hb]

def selfBody {rT : Type} (nextBit : Val rT) : Exp rT :=
  Exp.openRec 4 (readVal nextBit).fst (loopTemplate nextBit)

private theorem selfBody_lcb {rT : Type} (nextBit : Val rT) :
    Exp.lcb 4 (selfBody nextBit) = true :=
  Exp.lcb_openRec
    (Exp.lcb_mono (Exp.lc_imp_lcb (readVal nextBit).lc) (by decide : 0 ≤ 4))
    (loop_lcb nextBit)

def unfoldedVal {rT : Type} (nextBit : Val rT) : Val rT :=
  ⟨.lam (.lam (.lam (.lam (selfBody nextBit)))),
    .lam (Exp.lcb_imp_lc (selfBody_lcb nextBit)), Exp.lcb_imp_lc (selfBody_lcb nextBit)⟩

def nodeBody {rT : Type} (nextBit : Val rT) (node : Loc) : Exp rT :=
  Exp.openRec 3 (.lit (.loc node)) (selfBody nextBit)

private theorem nodeBody_lcb {rT : Type} (nextBit : Val rT) (node : Loc) :
    Exp.lcb 3 (nodeBody nextBit node) = true :=
  Exp.lcb_openRec (by simp [Exp.lcb]) (selfBody_lcb nextBit)

def nodeVal {rT : Type} (nextBit : Val rT) (node : Loc) : Val rT :=
  ⟨.lam (.lam (.lam (nodeBody nextBit node))),
    .lam (Exp.lcb_imp_lc (nodeBody_lcb nextBit node)),
    Exp.lcb_imp_lc (nodeBody_lcb nextBit node)⟩

def remainingBody {rT : Type} (nextBit : Val rT) (node : Loc) (remaining : ℤ) : Exp rT :=
  Exp.openRec 2 (.lit (.int remaining)) (nodeBody nextBit node)

private theorem remainingBody_lcb {rT : Type} (nextBit : Val rT) (node : Loc) (remaining : ℤ) :
    Exp.lcb 2 (remainingBody nextBit node remaining) = true :=
  Exp.lcb_openRec (by simp [Exp.lcb]) (nodeBody_lcb nextBit node)

def remainingVal {rT : Type} (nextBit : Val rT) (node : Loc) (remaining : ℤ) : Val rT :=
  ⟨.lam (.lam (remainingBody nextBit node remaining)),
    .lam (Exp.lcb_imp_lc (remainingBody_lcb nextBit node remaining)),
    Exp.lcb_imp_lc (remainingBody_lcb nextBit node remaining)⟩

def numeratorBody {rT : Type} (nextBit : Val rT) (node : Loc)
    (remaining numerator : ℤ) : Exp rT :=
  Exp.openRec 1 (.lit (.int numerator)) (remainingBody nextBit node remaining)

private theorem numeratorBody_lcb {rT : Type} (nextBit : Val rT) (node : Loc)
    (remaining numerator : ℤ) : Exp.lcb 1 (numeratorBody nextBit node remaining numerator) = true :=
  Exp.lcb_openRec (by simp [Exp.lcb]) (remainingBody_lcb nextBit node remaining)

def numeratorVal {rT : Type} (nextBit : Val rT) (node : Loc)
    (remaining numerator : ℤ) : Val rT :=
  ⟨.lam (numeratorBody nextBit node remaining numerator),
    .lam (Exp.lcb_imp_lc (numeratorBody_lcb nextBit node remaining numerator)),
    Exp.lcb_imp_lc (numeratorBody_lcb nextBit node remaining numerator)⟩

end SampLib.LatentDigits.Syntax
