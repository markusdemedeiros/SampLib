import SampLib.Samplers.RationalPowerInteger
import SampLib.Samplers.RationalCoin
import SampLib.CurriedStep
import SampLib.Syntax.ClosedExp
import Samplers.Bernoulli.Linear

/-! # The adaptive power walk's closed source template

The input coin remains bound while all nested lets and recursive binders are
constructed. It is inserted afterwards as an arbitrary locally closed value.
-/

open ProbLang

namespace SampLib.LinearPowerWalk.Syntax

set_option maxHeartbeats 800000

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := RationalCoin.rationalCoin_fv

scoped instance logistic_closed {rT : Type} : ClosedExp (Occil.logisticFactory : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.logisticFactory, Exp.fv, RationalCoin.rationalCoin_fv]

scoped instance iterate_closed {rT : Type} : ClosedExp (Occil.iterateCoin : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.iterateCoin, Exp.fv]

scoped instance power_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.rationalPower : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.rationalPower, Occil.iterateCoin, Occil.fractionalPower,
      Exp.fv, RationalCoin.rationalCoin_fv]

open scoped SampLib.LinearPowerWalk.Syntax

private def template {rT : Type} : Exp rT := pl%
  fun coin,
    rec draw remaining ca cb marginNum marginDen :=
      if remaining = #0 then #true else
      if #355 * marginDen < #100 * remaining * marginNum then
        let betaNum := #2 * marginDen - marginNum;
        let betaDen := #2 * (marginDen - marginNum);
        if &Occil.FactoryExtra.rationalPower
          (fun u, &Occil.rationalCoin betaDen betaNum) remaining #1 #()
        then draw remaining (ca * betaNum) (cb * betaDen) marginNum (#2 * marginDen)
        else #false
      else
        let next := (if &Occil.logisticFactory coin ca cb #()
          then remaining - #1 else remaining + #1);
        draw next ca cb marginNum marginDen

private def templateBody {rT : Type} : Exp rT :=
  match (template : Exp rT) with
  | .lam body => body
  | _ => .fail

def code {rT : Type} : Exp rT :=
  match (templateBody : Exp rT) with
  | .fix (.lam (.lam (.lam (.lam (.lam body))))) => body
  | _ => .fail

theorem code_lcb {rT : Type} : Exp.lcb 7 (code : Exp rT) = true := by lcb_decide

private theorem loop_lc {rT : Type} (coin : Val rT) :
    (Exp.fix (CurriedStep.lambdas 5 (Exp.openRec 6 coin.fst code))).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 1 (CurriedStep.lambdas 5 (Exp.openRec 6 coin.fst code)) = true
  rw [CurriedStep.lcb_lambdas]
  exact Exp.lcb_openRec (Exp.lcb_ofVal 6 coin) code_lcb

def loop {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.fix (CurriedStep.lambdas 5 (Exp.openRec 6 coin.fst code)),
    .fix (loop_lc coin), loop_lc coin⟩

def stepBody {rT : Type} (coin : Val rT) : Exp rT :=
  Exp.openRec 5 (loop coin).fst (Exp.openRec 6 coin.fst code)

theorem stepBody_lcb {rT : Type} (coin : Val rT) : Exp.lcb 5 (stepBody coin) = true :=
  Exp.lcb_openRec (Exp.lcb_ofVal 5 (loop coin))
    (Exp.lcb_openRec (Exp.lcb_ofVal 6 coin) code_lcb)

def step {rT : Type} (coin : Val rT) (n a b e f : ℤ) :
    {term : Exp rT // CurriedStep.opened [Val.int n, .int a, .int b, .int e, .int f]
      (stepBody coin) = term} := by
  refine ⟨_, by
    conv_lhs =>
      simp [CurriedStep.opened, stepBody, code, templateBody, template,
        Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal, Var.internal.injEq,
        ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]⟩

theorem opened_step {rT : Type} (coin : Val rT) (n a b e f : ℤ) :
    CurriedStep.opened [Val.int n, .int a, .int b, .int e, .int f] (stepBody coin) =
      (step coin n a b e f).val := (step coin n a b e f).property

def contracting {rT : Type} (coin : Val rT) (a b : ℤ) : Val rT :=
  ⟨.lam pl(if &Occil.rationalCoin #int a #int b then &coin.fst #() else #false),
    .lam (by is_lc), by is_lc⟩

/-- The source guards and initial loop application, with structural binders finalized. -/
def body {rT : Type} (coin : Val rT) (a b n e f : ℤ) : Exp rT :=
  let run : Exp rT := pl({Exp.bvar 0} #int n #int a #int b #int e #int f)
  let expanding := Exp.app (.lam run) (loop coin).fst
  pl% if (#int a < #0) || (#int b <= #0) || (#int n < #0) then fail else
    if #int a <= #int b then &Occil.iterateCoin &(contracting coin a b).fst #int n
    else if (#int e <= #0) || (#int f <= #int e) then fail else &expanding

def sourceBody {rT : Type} : Exp rT :=
  match (Occil.FactoryExtra.linearPowerWalk : Exp rT) with
  | .lam (.lam (.lam (.lam (.lam (.lam (.lam body)))))) => body
  | _ => .fail

theorem source_eq {rT : Type} : (Occil.FactoryExtra.linearPowerWalk : Exp rT) =
    CurriedStep.lambdas 7 sourceBody := by kernel_rfl

theorem sourceBody_lcb {rT : Type} : Exp.lcb 7 (sourceBody : Exp rT) = true := by
  lcb_decide

def arguments {rT : Type} (coin : Val rT) (a b n e f : ℤ) : List (Val rT) :=
  [coin, .int a, .int b, .int n, .int e, .int f, .unit]

theorem opened_source {rT : Type} (coin : Val rT) (a b n e f : ℤ) :
    CurriedStep.opened (arguments coin a b n e f) sourceBody = body coin a b n e f := by
  simp [CurriedStep.opened, arguments, sourceBody, Occil.FactoryExtra.linearPowerWalk,
    body, contracting, loop, code, templateBody, template, CurriedStep.lambdas,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]

end SampLib.LinearPowerWalk.Syntax
