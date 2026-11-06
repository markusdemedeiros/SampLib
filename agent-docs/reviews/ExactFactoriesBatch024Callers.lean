import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.LinearPowerWalk

open Lean Meta Elab Command

private partial def stripLets (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => stripLets (body.instantiate1 value)
  | e => e

private partial def parameterIndex (name : Name) (e : Expr) (i : Nat := 0) : Option Nat :=
  match e with
  | .forallE n _ body _ => if n == name then some i else parameterIndex name body (i + 1)
  | .mdata _ body => parameterIndex name body i
  | _ => none

private partial def programHead (e : Expr) : Expr :=
  let e := stripLets e
  if e.getAppFn.isConstOf ``ProbLang.Exp.app then
    let args := e.getAppArgs
    if args.size ≥ 2 then programHead args[args.size - 2]! else e
  else e

private partial def containsOwnSpec (target : Name) (fuel : Nat) (e : Expr) : MetaM Bool := do
  if fuel == 0 then throwError "Premise inspection exhausted its structural bound"
  let e ← withTransparency .reducible (whnf (stripLets e))
  let e := stripLets e
  let head := e.getAppFn
  if head.isConstOf ``SampLib.IsDistSpec || head.isConstOf ``SampLib.IsOwnedDistSpec then
    let specInfo ← getConstInfo head.constName!
    let some index := parameterIndex `e specInfo.type
      | throwError "Cannot locate distribution specification's program parameter"
    let args := e.getAppArgs
    if index < args.size then
      return (programHead args[index]!).getAppFn.isConstOf target
    return false
  match e with
  | .forallE n domain body bi =>
      if (← containsOwnSpec target (fuel - 1) domain) then return true
      withLocalDecl n bi domain fun x =>
        containsOwnSpec target (fuel - 1) (body.instantiate1 x)
  | .lam n domain body bi =>
      withLocalDecl n bi domain fun x =>
        containsOwnSpec target (fuel - 1) (body.instantiate1 x)
  | _ =>
      if [``And, ``Or, ``Iff, ``Exists].any (fun name => head.isConstOf name) then
        for arg in e.getAppArgs do
          if (← containsOwnSpec target (fuel - 1) arg) then return true
      return false

private def auditSpecification (theoremName samplerName specName : Name) : CommandElabM Unit := do
  let info ← getConstInfo theoremName
  let specInfo ← getConstInfo specName
  let label := if specName == ``SampLib.IsDistSpec then "IsDistSpec" else "IsOwnedDistSpec"
  let some index := parameterIndex `e specInfo.type
    | throwError "Cannot locate {label}'s program parameter"
  let _ ← getConstInfo samplerName
  liftTermElabM do
    forallTelescopeReducing info.type fun params result => do
      let result := stripLets result
      unless result.getAppFn.isConstOf specName do
        throwError "{theoremName} does not conclude with {label}"
      let args := result.getAppArgs
      unless index < args.size do throwError "Incomplete {label} application"
      unless (programHead args[index]!).getAppFn.isConstOf samplerName do
        throwError "{theoremName} does not specify a call to {samplerName}"
      for param in params do
        let premise ← inferType param
        if (← containsOwnSpec samplerName 128 premise) then
          throwError "{theoremName} assumes its own concrete sampler in a premise"
      logInfo m!"SPEC_OK {theoremName} {samplerName}"

elab "#audit_dist_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.IsDistSpec

elab "#audit_owned_dist_spec " theoremName:ident " for " samplerName:ident : command =>
  auditSpecification theoremName.getId samplerName.getId ``SampLib.IsOwnedDistSpec



open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview024

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E p a b e f h n coin hcoin) F I

private def quarter : unitInterval := ⟨1/4, by norm_num, by norm_num⟩

private theorem expanded : LinearFactory.Admissible quarter 2 1 1 2 := by
  norm_num [LinearFactory.Admissible, Gambler.ratio, quarter]

private theorem expanded_zero : LinearFactory.Admissible 0 2 1 1 2 := by
  norm_num [LinearFactory.Admissible, Gambler.ratio]

private theorem zero_coefficient : LinearFactory.Admissible 1 0 1 (-10) 0 := by
  norm_num [LinearFactory.Admissible]

private theorem identity : LinearFactory.Admissible 1 1 1 (-10) 0 := by
  norm_num [LinearFactory.Admissible]

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law quarter) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E quarter 2 1 1 2 expanded 8 coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law quarter) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E quarter 2 1 1 2 expanded 1 coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E 0 2 1 1 2 expanded_zero 8 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E 1 0 1 (-10) 0 zero_coefficient 0 coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E 1 0 1 (-10) 0 zero_coefficient 4 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (LinearPowerWalk.linearPowerWalk_distSpec E 1 1 1 (-10) 0 identity 4 coin hcoin)
    (fun b => if b then 0 else ∞) I

example : (IterateCoin.bias (LinearFactory.bias quarter 2 1 1 2 expanded) 8 : ℝ) = 1/256 := by
  norm_num [IterateCoin.bias, quarter]

example : IterateCoin.credit (LinearFactory.bias 1 0 1 (-10) 0 zero_coefficient) 0
    (fun b => if b then 0 else ∞) = 0 := by
  simp [IterateCoin.credit, IterateCoin.bias, RealCoin.credit, RealCoin.pmf]

example : IterateCoin.credit (LinearFactory.bias 0 2 1 1 2 expanded_zero) 8
    (fun b => if b then ∞ else 0) = 0 := by
  simp [IterateCoin.credit, IterateCoin.bias, RealCoin.credit, RealCoin.pmf]

#print axioms LinearPowerWalk.linearPowerWalk_distSpec
#print axioms LinearPowerWalk.twp_linearPowerWalk
#print axioms AdaptivePowerWalk.expectation
#print axioms AdaptivePowerWalk.walk_budget_drift
#print axioms AdaptivePowerWalk.amplification_budget_drift

end

end ExactFactoriesReview024

#audit_dist_spec SampLib.LinearPowerWalk.linearPowerWalk_distSpec for Occil.FactoryExtra.linearPowerWalk
