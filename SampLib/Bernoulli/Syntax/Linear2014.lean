import SampLib.Bernoulli.Syntax.LinearPowerWalk
import SampLib.Discrete.Geometric

/-! # Structural source opening for Huber's geometric-jump factory -/

open ProbLang
open scoped SampLib.LinearPowerWalk.Syntax

namespace SampLib.Linear2014.Syntax

scoped instance geometric_closed {rT : Type} : ClosedExp (Occil.geometric : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.geometric, Exp.fv]

open scoped SampLib.Linear2014.Syntax

private def template {rT : Type} : Exp rT := pl%
  fun coin,
    rec draw state ca cb en ed thresholdNum thresholdDen :=
      let afterStep := state - #1;
      let next := (if coin #() then afterStep else
        afterStep + #1 + &Occil.geometric (fun u, &Occil.rationalCoin (ca - cb) ca) #());
      if next = #0 then #true else
      if next * thresholdDen < thresholdNum then draw next ca cb en ed thresholdNum thresholdDen
      else
        let factorNum := #2 * ed + en;
        let factorDen := #2 * ed;
        if &Occil.FactoryExtra.rationalPower
          (fun u, &Occil.rationalCoin factorDen factorNum) next #1 #()
        then draw next (ca * factorNum) (cb * factorDen) en (#2 * ed)
          (#2 * thresholdNum) thresholdDen
        else #false

private def templateBody {rT : Type} : Exp rT :=
  match (template : Exp rT) with
  | .lam body => body
  | _ => .fail

def code {rT : Type} : Exp rT :=
  match (templateBody : Exp rT) with
  | .fix (.lam (.lam (.lam (.lam (.lam (.lam (.lam body))))))) => body
  | _ => .fail

theorem code_lcb {rT : Type} : Exp.lcb 9 (code : Exp rT) = true := by lcb_decide

private theorem loop_lc {rT : Type} (coin : Val rT) :
    (Exp.fix (CurriedStep.lambdas 7 (Exp.openRec 8 coin.fst code))).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 1 (CurriedStep.lambdas 7 (Exp.openRec 8 coin.fst code)) = true
  rw [CurriedStep.lcb_lambdas]
  exact Exp.lcb_openRec (Exp.lcb_ofVal 8 coin) code_lcb

def loop {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.fix (CurriedStep.lambdas 7 (Exp.openRec 8 coin.fst code)),
    .fix (loop_lc coin), loop_lc coin⟩

def stepBody {rT : Type} (coin : Val rT) : Exp rT :=
  Exp.openRec 7 (loop coin).fst (Exp.openRec 8 coin.fst code)

theorem stepBody_lcb {rT : Type} (coin : Val rT) : Exp.lcb 7 (stepBody coin) = true :=
  Exp.lcb_openRec (Exp.lcb_ofVal 7 (loop coin))
    (Exp.lcb_openRec (Exp.lcb_ofVal 8 coin) code_lcb)

def step {rT : Type} (coin : Val rT) (n a b e f numerator denominator : ℤ) :
    {term : Exp rT // CurriedStep.opened
      [Val.int n, .int a, .int b, .int e, .int f, .int numerator, .int denominator]
      (stepBody coin) = term} := by
  refine ⟨_, by
    conv_lhs =>
      simp [CurriedStep.opened, stepBody, code, templateBody, template,
        Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal, Var.internal.injEq,
        ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]⟩

theorem opened_step {rT : Type} (coin : Val rT) (n a b e f numerator denominator : ℤ) :
    CurriedStep.opened
      [Val.int n, .int a, .int b, .int e, .int f, .int numerator, .int denominator]
      (stepBody coin) = (step coin n a b e f numerator denominator).val :=
  (step coin n a b e f numerator denominator).property

/-- Nested lets are assembled structurally, so an arbitrary callback cannot be captured. -/
def body {rT : Type} (coin : Val rT) (a b e f : ℤ) : Exp rT :=
  let run : Exp rT := pl({Exp.bvar 0} #1 #int a #int b {Exp.bvar 2} {Exp.bvar 1}
    (#23 * {Exp.bvar 1}) (#5 * {Exp.bvar 2}))
  let loopLet := Exp.app (.lam run) (loop coin).fst
  let denominatorLet := Exp.app (.lam loopLet) pl(snd({Exp.bvar 1}))
  let numeratorLet := Exp.app (.lam denominatorLet) pl(fst({Exp.bvar 0}))
  let initial := Exp.app (.lam numeratorLet)
    pl(if #1000 * #int e <= #644 * #int f then (#int e, #int f) else (#644, #1000))
  pl% if (#int a < #0) || (#int b <= #0) then fail else
    if #int a <= #int b then
      if &Occil.rationalCoin #int a #int b then &coin.fst #() else #false
    else if (#int e <= #0) || (#int f <= #int e) then fail else &initial

def sourceBody {rT : Type} : Exp rT :=
  match (Occil.FactoryExtra.linear2014 : Exp rT) with
  | .lam (.lam (.lam (.lam (.lam (.lam body))))) => body
  | _ => .fail

theorem source_eq {rT : Type} : (Occil.FactoryExtra.linear2014 : Exp rT) =
    CurriedStep.lambdas 6 sourceBody := by kernel_rfl

theorem sourceBody_lcb {rT : Type} : Exp.lcb 6 (sourceBody : Exp rT) = true := by
  lcb_decide

def arguments {rT : Type} (coin : Val rT) (a b e f : ℤ) : List (Val rT) :=
  [coin, .int a, .int b, .int e, .int f, .unit]

theorem opened_source {rT : Type} (coin : Val rT) (a b e f : ℤ) :
    CurriedStep.opened (arguments coin a b e f) sourceBody = body coin a b e f := by
  simp [CurriedStep.opened, arguments, sourceBody, Occil.FactoryExtra.linear2014,
    body, loop, code, templateBody, template, CurriedStep.lambdas,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]

end SampLib.Linear2014.Syntax
