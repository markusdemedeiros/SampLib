import SampLib.Core.CurriedStep
import SampLib.Latent.Syntax.PSRNDigits
import SampLib.PSRN.Syntax.ExponentialCount
import SampLib.PSRN.Support.PSRNExponentialLogistic

/-! # The decay-based exponential constructor's literal nested closures -/

open ProbLang

namespace SampLib.PSRNExponential.Program

open scoped SampLib.LatentDigits.Syntax

scoped instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.PSRNExponential.Program

def bind {rT : Type} (e body : Exp rT) : Exp rT := .app (.lam body) e

def digits {rT : Type} (decay : Val rT) : Exp rT :=
  pl(&Occil.PSRN.newByDigits &(ExponentialLogistic.Program.digitVal decay).fst #())

def afterDigits {rT : Type} (whole : ℤ) : Exp rT :=
  .app (.app Occil.PSRN.add
    (.app (.app Occil.PSRN.rational (.lit (.int whole))) (.lit (.int 1)))) (.bvar 0)

def afterWhole {rT : Type} (decay : Val rT) : Exp rT :=
  bind (digits decay)
    (.app (.app Occil.PSRN.add
      (.app (.app Occil.PSRN.rational (.bvar 1)) (.lit (.int 1)))) (.bvar 0))

def afterCount {rT : Type} (decay : Val rT) : Exp rT :=
  bind (.app (.bvar 0) (.lit (.int 0))) (afterWhole decay)

def body {rT : Type} (decay : Val rT) : Exp rT :=
  bind (ExponentialCount.Program.countVal decay).fst (afterCount decay)

/-- Body after the integer-part closure is bound, before running it. -/
def countBody {rT : Type} (decay : Val rT) : Exp rT :=
  bind (.app (ExponentialCount.Program.countVal decay).fst (.lit (.int 0))) (afterWhole decay)

/-- Body after observing the integer part, before constructing its conditional digits. -/
def wholeBody {rT : Type} (decay : Val rT) (whole : ℤ) : Exp rT :=
  bind (digits decay) (afterDigits whole)

theorem afterWhole_lcb {rT : Type} (decay : Val rT) :
    Exp.lcb 1 (afterWhole decay) = true := by
  have hd (k : ℕ) : Exp.lcb k (ExponentialLogistic.Program.digitVal decay).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (ExponentialLogistic.Program.digitVal decay).lc) (Nat.zero_le k)
  have hn (k : ℕ) : Exp.lcb k (Occil.PSRN.newByDigits : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (LatentDigits.Syntax.constructor_closed (rT := rT)).lc)
      (Nat.zero_le k)
  have ha (k : ℕ) : Exp.lcb k (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (add_closed (rT := rT)).lc) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k (Occil.PSRN.rational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (rational_closed (rT := rT)).lc) (Nat.zero_le k)
  simp [afterWhole, digits, bind, Exp.lcb, hd, hn, ha, hr]

theorem afterWhole_lc {rT : Type} (decay : Val rT) :
    (Exp.lam (afterWhole decay)).IsLocallyClosed := Exp.lcb_imp_lc (afterWhole_lcb decay)

theorem afterCount_lc {rT : Type} (decay : Val rT) :
    (Exp.lam (afterCount decay)).IsLocallyClosed := by
  have hwhole := afterWhole_lcb (rT := rT) decay
  apply Exp.lcb_imp_lc
  change (Exp.lcb 2 (afterWhole decay) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨Exp.lcb_mono hwhole (by decide : 1 ≤ 2), rfl⟩

theorem afterDigits_lc {rT : Type} (whole : ℤ) :
    (Exp.lam (afterDigits (rT := rT) whole)).IsLocallyClosed := by
  have ha (k : ℕ) : Exp.lcb k (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (add_closed (rT := rT)).lc) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k (Occil.PSRN.rational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (rational_closed (rT := rT)).lc) (Nat.zero_le k)
  apply Exp.lcb_imp_lc
  simp [afterDigits, Exp.lcb, ha, hr]

def sourceBody {rT : Type} : Exp rT :=
  match (Occil.PSRN.newExponentialFromDecay : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

theorem source_eq {rT : Type} : (Occil.PSRN.newExponentialFromDecay : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

theorem sourceBody_lcb {rT : Type} : Exp.lcb 2 (sourceBody : Exp rT) = true := by
  lcb_decide

/-- Arbitrary callback free variables survive both constructor beta steps. -/
theorem opened_source {rT : Type} (decay : Val rT) :
    CurriedStep.opened [decay, .unit] sourceBody = body decay := by
  simp [CurriedStep.opened, sourceBody, Occil.PSRN.newExponentialFromDecay, body,
    afterCount, afterWhole, digits, bind, ExponentialCount.Program.countVal,
    ExponentialCount.Program.countCode, ExponentialLogistic.Program.digitVal,
    ExponentialLogistic.Program.digitBody, ExponentialLogistic.Program.loopCode,
    ExponentialLogistic.Program.body, Exp.openRec, Exp.close, Exp.closeRec,
    Var.internal.injEq, ClosedExp.openRec, ClosedExp.closeRec,
    FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec, ProbLang.openRec_val_fst]

theorem opened_afterCount {rT : Type} (decay : Val rT) :
    Exp.open' (afterCount decay) (ExponentialCount.Program.countVal decay).fst =
      countBody decay := by
  simp [afterCount, countBody, afterWhole, digits, bind, Exp.open', Exp.openRec,
    ClosedExp.openRec, ProbLang.openRec_val_fst]

theorem opened_afterWhole {rT : Type} (decay : Val rT) (whole : ℤ) :
    Exp.open' (afterWhole decay) (.lit (.int whole)) = wholeBody decay whole := by
  simp [afterWhole, wholeBody, afterDigits, digits, bind, Exp.open', Exp.openRec,
    ClosedExp.openRec, ProbLang.openRec_val_fst]

theorem opened_afterDigits {rT : Type} (whole : ℤ) (value : Val rT) :
    Exp.open' (afterDigits whole) value.fst =
      pl(&Occil.PSRN.add (&Occil.PSRN.rational #whole #1) &value.fst) := by
  simp [afterDigits, Exp.open', Exp.openRec, ClosedExp.openRec]

end SampLib.PSRNExponential.Program
