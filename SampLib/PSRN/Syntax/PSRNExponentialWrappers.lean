import SampLib.PSRN.Syntax.PSRNExponential
import SampLib.PSRN.Support.Exponential.RationalRateDecay
import SampLib.PSRN.Support.Exponential.LogRateDecay
import SampLib.PSRN.Support.Exponential.UnknownRateDecay

/-! # Literal source wrappers for the exponential rate interfaces -/

open ProbLang

namespace SampLib.PSRNExponential.Wrappers

scoped instance decay_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newExponentialFromDecay : Exp rT) where
  lc := by
    rw [Program.source_eq]
    exact CurriedStep.lambdas_lc 2 Program.sourceBody (Program.sourceBody_lcb (rT := rT))
  fv := by kernel_rfl

scoped instance power_closed {rT : Type} : ClosedExp (Occil.PSRN.powerCoin : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance factory_closed {rT : Type} : ClosedExp (Occil.expMinusFactory : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.PSRNExponential.Wrappers

def rationalBody {rT : Type} (a b : ℤ) : Exp rT :=
  pl(if (#a <= #0) || (#b <= #0) then fail else
    &Occil.PSRN.newExponentialFromDecay &(PSRNRationalRateDecay.value a b).fst #())

def logBody {rT : Type} (x y : ℤ) : Exp rT :=
  pl(if (#y <= #0) || (#x <= #y) then fail else
    &Occil.PSRN.newExponentialFromDecay &(PSRNLogRateDecay.value x y).fst #())

def unknownBody {rT : Type} (coin : Val rT) : Exp rT :=
  pl(&Occil.PSRN.newExponentialFromDecay &(PSRNUnknownRateDecay.value coin).fst #())

def rationalSource {rT : Type} : Exp rT :=
  match (Occil.PSRN.newExponential : Exp rT) with
  | .lam (.lam (.lam body)) => body
  | _ => .fail

def logSource {rT : Type} : Exp rT :=
  match (Occil.PSRN.newExponentialLogRate : Exp rT) with
  | .lam (.lam (.lam body)) => body
  | _ => .fail

def unknownSource {rT : Type} : Exp rT :=
  match (Occil.PSRN.newExponentialUnknownRate : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

theorem rational_source_eq {rT : Type} : (Occil.PSRN.newExponential : Exp rT) =
    CurriedStep.lambdas 3 rationalSource := by kernel_rfl

theorem log_source_eq {rT : Type} : (Occil.PSRN.newExponentialLogRate : Exp rT) =
    CurriedStep.lambdas 3 logSource := by kernel_rfl

theorem unknown_source_eq {rT : Type} : (Occil.PSRN.newExponentialUnknownRate : Exp rT) =
    CurriedStep.lambdas 2 unknownSource := by kernel_rfl

theorem rational_lcb {rT : Type} : Exp.lcb 3 (rationalSource : Exp rT) = true := by lcb_decide

theorem log_lcb {rT : Type} : Exp.lcb 3 (logSource : Exp rT) = true := by lcb_decide

theorem unknown_lcb {rT : Type} : Exp.lcb 2 (unknownSource : Exp rT) = true := by lcb_decide

theorem rational_opened {rT : Type} (a b : ℤ) :
    CurriedStep.opened [.int a, .int b, .unit] rationalSource = (rationalBody (rT := rT) a b) := by
  simp [CurriedStep.opened, rationalSource, Occil.PSRN.newExponential, rationalBody,
    PSRNRationalRateDecay.value, PSRNRationalRateDecay.body,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ExpMinusRational.expMinusRational_openRec, ExpMinusRational.expMinusRational_closeRec,
    ClosedExp.openRec, ClosedExp.closeRec]

theorem log_opened {rT : Type} (x y : ℤ) :
    CurriedStep.opened [.int x, .int y, .unit] logSource = (logBody (rT := rT) x y) := by
  simp [CurriedStep.opened, logSource, Occil.PSRN.newExponentialLogRate, logBody,
    PSRNLogRateDecay.value, PSRNLogRateDecay.body, PSRNLogRateDecay.coin,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, RationalCoin.rationalCoin_openRec,
    RationalCoin.rationalCoin_closeRec]

theorem unknown_opened {rT : Type} (coin : Val rT) :
    CurriedStep.opened [coin, .unit] unknownSource = unknownBody coin := by
  simp [CurriedStep.opened, unknownSource, Occil.PSRN.newExponentialUnknownRate, unknownBody,
    PSRNUnknownRateDecay.value, PSRNUnknownRateDecay.body,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, RationalCoin.rationalCoin_openRec,
    RationalCoin.rationalCoin_closeRec, ProbLang.openRec_val_fst]

end SampLib.PSRNExponential.Wrappers
