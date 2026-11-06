module

public import Metrology.TotalEris.WpTactics
public meta import Metrology.TotalEris.WpTactics
public meta import Metrology.Meta.AppByName

/-! # A pure CTE step with caller-controlled normalization

`twp_step` applies the same checked context rule as `twp_pure`, retaining the
symbolic reduct. Closedness rewrites can then remove openings of large recursive
constants before their bodies are traversed.
-/

@[expose] public section

namespace SampLib

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode ProbLang ProbLang.TotalEris
open ErisWpGS

/-- Take exactly one pure step, leaving its syntactic reduct unnormalized. -/
elab "twp_step" focus:(ppSpace colGt term:max)? : tactic =>
  ProofModeM.runTactic `twp_step fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "expected an IProp goal at universe level zero"
    let ~q(IProp $GF) := prop | throwError "expected an IProp goal"
    let ~q(UPred.instBIUPred) := bi | throwError "expected the BI of IProp"
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ErisWpGS.tglWp do
      throwError "expected a tglWp goal"
    let args := goalE.getAppArgs
    unless args.size == 11 do throwError "unexpected tglWp arity"
    have α : Q(Type) := args[0]!
    have instMS : Q(MeasurableSpace $α) := args[1]!
    have instPL : Q(@LawfulProbLangℝ $α $instMS) := args[2]!
    have instPD : Q(@ProbLangDist $α $instMS) := args[3]!
    have instFFI : Q(@ProbLangFFI $α $instMS) := args[4]!
    have instObs : Q(@ProbLangObs $α $instMS) := args[5]!
    have instWp : Q(ErisWpGS (rT := $α) $GF) := args[7]!
    have E : Q(CoPset) := args[8]!
    have e : Q(Exp $α) := args[9]!
    have Φ : Q(Val $α → IProp $GF) := args[10]!
    let focus? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let some res ← findPureStep instMS instPL instPD instFFI instObs e focus?
      | throwTacticEx `twp_step mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    let step := res.result
    let φ : Q(Prop) ← instantiateMVars step.φ
    let n : Q(Nat) ← instantiateMVars step.n
    let e₁ : Q(Exp $α) ← instantiateMVars step.e₁
    let raw : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ ← match res.e' with
      | ~q(.app $f $v) => do
          let f' : Q(Exp $α) ← pure (← whnf f).consumeMData
          match f' with
          | ~q(.fix $body) => pure q(.app (.open' $body $f) $v)
          | _ => pure raw
      | _ => pure raw
    let inner ← fillQ K e₂
    let pf ← addBIGoal hyps
      q(@tglWp $α $instMS $instPL $instPD $instFFI $instObs $GF $instWp $E $inner $Φ)
    let Hφ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    (← evalTacticAt (← `(tactic| (try is_value))) Hφ.mvarId!).forM addMVarGoal
    let stepPf ← mkAppByName ``ErisWpGS.twp_pure_step_ctx
      [(`rT, α), (`GF, GF), (`K, K), (`φ, φ), (`n, n), (`e₁, e₁), (`e₂, e₂), (`Hφ, Hφ),
        (`E, E), (`Φ, Φ)] [instMS, instPL, instPD, instFFI, instObs, instWp, step.inst]
    mvar.assign (← mkAppM ``BI.BIBase.Entails.trans #[pf, stepPf])

end SampLib
