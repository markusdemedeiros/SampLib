import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.TwoCoinPower
import SampLib.Common.RationalPower

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

namespace ExactFactoriesReview017

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

example (E : CoPset) (p q : unitInterval) (hstop : 0 < (p : ℝ) ∨ 0 < (q : ℝ))
    (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TwoCoinPower.twoCoinPower_distSpec E p q hstop base exponent hbase hexponent) F I

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (RationalPower.rationalPower_distSpec E p a b hb coin hcoin) F I

example (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (RationalPower.rationalPowerCoin_distSpec E p a b hb coin hcoin) F I

example (E : CoPset) (q : unitInterval) (hq : 0 < (q : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law 0) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool)
    (I : IProp GF) :=
  frame (TwoCoinPower.twoCoinPower_distSpec E 0 q (.inr hq) base exponent hbase hexponent)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (TwoCoinPower.twoCoinPower_distSpec E p 0 (.inl hp) base exponent hbase hexponent)
    (fun b => if b then 0 else ∞) I

example : ¬ (0 < ((0 : unitInterval) : ℝ) ∨ 0 < ((0 : unitInterval) : ℝ)) := by simp

example (q : unitInterval) (hq : 0 < (q : ℝ)) :
    RealCoin.credit (TwoCoinPower.bias 0 q) (fun b => if b then ∞ else 0) = 0 := by
  simp [TwoCoinPower.bias, FractionalPower.powerBias, Real.zero_rpow hq.ne',
    RealCoin.credit, RealCoin.pmf]

example (p : unitInterval) :
    RealCoin.credit (TwoCoinPower.bias p 0) (fun b => if b then 0 else ∞) = 0 := by
  simp [TwoCoinPower.bias, FractionalPower.powerBias, RealCoin.credit, RealCoin.pmf]

example : (RationalPower.bias 0 0 3 (by decide) : ℝ) = 1 := by
  norm_num [RationalPower.bias]

example : (RationalPower.bias 0 5 3 (by decide) : ℝ) = 0 := by
  norm_num [RationalPower.bias]

example : (RationalPower.bias 1 5 3 (by decide) : ℝ) = 1 := by
  norm_num [RationalPower.bias]

example : RealCoin.credit (RationalPower.bias 0 5 3 (by decide))
    (fun b => if b then ∞ else 0) = 0 := by
  norm_num [RationalPower.bias, RealCoin.credit, RealCoin.pmf]

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (RationalPower.rationalPower_distSpec E 0 0 3 (by decide) coin hcoin)
    (fun bit => if bit then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (RationalPower.rationalPower_distSpec E 0 6 3 (by decide) coin hcoin)
    (fun bit => if bit then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (RationalPower.rationalPowerCoin_distSpec E 0 5 3 (by decide) coin hcoin)
    (fun bit => if bit then ∞ else 0) I

#print axioms TwoCoinPower.twoCoinPower_distSpec
#print axioms RationalPower.rationalPower_distSpec
#print axioms RationalPower.rationalPowerCoin_distSpec
#print axioms RationalPower.expectation
#print axioms RationalPower.power_split

end

end ExactFactoriesReview017

#audit_dist_spec SampLib.TwoCoinPower.twoCoinPower_distSpec for Occil.FactoryExtra.twoCoinPower
#audit_dist_spec SampLib.RationalPower.rationalPower_distSpec for Occil.FactoryExtra.rationalPower
#audit_dist_spec SampLib.RationalPower.rationalPowerCoin_distSpec for Occil.DiscreteExtra.rationalPowerCoin
