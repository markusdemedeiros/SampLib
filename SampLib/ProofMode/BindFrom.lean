module

public import Metrology.TotalEris.WpTactics
public meta import Metrology.TotalEris.WpTactics
public meta import Metrology.Meta.AppByName

/-! # Binding the program named by a known TWP theorem

`twp_bind_from h` uses the program in the type of `h` as its focus. It applies
the ordinary context rule; the theorem itself is applied separately. This keeps
recursive calls folded after explicit closedness normalization of their specs.
-/

@[expose] public section

namespace SampLib

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode ProbLang ProbLang.TotalEris
open ErisWpGS

private meta partial def findWpProgram (e : LeanExpr) : Option LeanExpr :=
  let e := e.consumeMData
  if e.getAppFn.isConstOf ``ErisWpGS.tglWp then
    let args := e.getAppArgs
    if args.size == 11 then some args[9]! else none
  else match e with
    | .app f x => (findWpProgram f).orElse (fun _ => findWpProgram x)
    | .mdata _ b => findWpProgram b
    | _ => none

/-- Bind the program of an instantiated TWP theorem, without unfolding its assertion. -/
elab "twp_bind_from" colGt ppSpace theoremTerm:term:max : tactic =>
  ProofModeM.runTactic `twp_bind_from fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "expected an IProp goal at universe level zero"
    let ~q(IProp $GF) := prop | throwError "expected an IProp goal"
    let ~q(UPred.instBIUPred) := bi | throwError "expected the BI of IProp"
    let goalE := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.isConstOf ``ErisWpGS.tglWp do
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
    let proof ← Term.elabTerm theoremTerm none
    let proofType ← instantiateMVars (← inferType proof)
    let some focus := findWpProgram proofType
      | throwError "expected an instantiated theorem whose type contains a tglWp"
    unless ← isDefEq (← inferType focus) q(Exp $α) do
      throwError "the theorem specifies a different probabilistic language"
    let some res ← findECtx e (fun candidate => do guard (← isDefEq candidate focus))
      | throwTacticEx `twp_bind_from mvar "the theorem's program is not an evaluation focus"
    have K : Q(Ectx $α) := res.K
    have e' : Q(Exp $α) := focus
    let Φc : Q(Val $α → IProp $GF) ← withLocalDeclDQ `v q(Val $α) fun v => do
      let body ← fillQ K q(Exp.ofVal $v)
      mkLambdaFVars #[v]
        q(@tglWp $α $instMS $instPL $instPD $instFFI $instObs $GF $instWp $E $body $Φ)
    let pf ← addBIGoal hyps
      q(@tglWp $α $instMS $instPL $instPD $instFFI $instObs $GF $instWp $E $e' $Φc)
    let bindPf ← mkAppByName ``ErisWpGS.tglWp_bind
      [(`rT, α), (`GF, GF), (`K, K), (`E, E), (`e, e'), (`Φ, Φ)]
      [instMS, instPL, instPD, instFFI, instObs, instWp]
    mvar.assign (← mkAppM ``BI.BIBase.Entails.trans #[pf, bindPf])

end SampLib
