import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.MinimumHalf
import SampLib.Bernoulli.ThreePointPiecewise

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

namespace ExactFactoriesReview027

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

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (MinimumComplement.minimumComplement_distSpec E p coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (MinimumComplement.minimumHalf_distSpec E p coin hcoin) F I

example (E : CoPset) (p μ ν : unitInterval) (coin mu nu : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hmu : IsDistSpec (GF := GF) E pl(&mu.fst #()) (RealCoin.law μ) Val.bool)
    (hnu : IsDistSpec (GF := GF) E pl(&nu.fst #()) (RealCoin.law ν) Val.bool)
    (mode : Fin 6) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (MinimumComplement.threePointPiecewise_distSpec E p μ ν
    coin mu nu hcoin hmu hnu mode) F I

private def fairCallback : Val rT :=
  ⟨.lam pl(&Occil.fairCoin #()), .lam (by is_lc), by is_lc⟩

private theorem fairCallback_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(fairCallback : Val rT).fst #())
      (RealCoin.law VonNeumann.fairBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [FairCoin.fairCoin_openRec]
    iapply (FairCoin.fairCoin_distSpec E).spec F hF $$ Hcredit

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (MinimumComplement.minimumComplement_distSpec E VonNeumann.fairBias
    fairCallback (fairCallback_spec E)) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (MinimumComplement.minimumComplement_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (MinimumComplement.minimumComplement_distSpec E 1 coin hcoin)
    (fun b => if b then ∞ else 0) I

example : (MinimumComplement.bias VonNeumann.fairBias : ℝ) = 1/2 := by
  norm_num [MinimumComplement.bias, VonNeumann.fairBias]

example : (MinimumComplement.halfBias 1 : ℝ) = 1/2 := by
  norm_num [MinimumComplement.halfBias]

example : RealCoin.credit (MinimumComplement.bias 0)
    (fun b => if b then ∞ else 0) = 0 := by
  norm_num [MinimumComplement.bias, RealCoin.credit, RealCoin.pmf]

example : RealCoin.credit (MinimumComplement.bias 1)
    (fun b => if b then ∞ else 0) = 0 := by
  norm_num [MinimumComplement.bias, RealCoin.credit, RealCoin.pmf]

example (μ ν : unitInterval) : (MinimumComplement.piecewiseBias 0 μ ν 4 : ℝ) = 1 := by
  rw [MinimumComplement.piecewiseBias_coe]
  norm_num

example (μ ν : unitInterval) : (MinimumComplement.piecewiseBias 1 μ ν 3 : ℝ) = 0 := by
  rw [MinimumComplement.piecewiseBias_coe]
  norm_num

example (μ ν : unitInterval) :
    (MinimumComplement.piecewiseBias VonNeumann.fairBias μ ν 1 : ℝ) = 1/2 := by
  rw [MinimumComplement.piecewiseBias_coe]
  norm_num [VonNeumann.fairBias]
  ring

example (μ ν : unitInterval) : RealCoin.credit (MinimumComplement.piecewiseBias 0 μ ν 4)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, MinimumComplement.piecewiseBias_coe]

#print axioms MinimumComplement.minimumComplement_distSpec
#print axioms MinimumComplement.minimumHalf_distSpec
#print axioms MinimumComplement.threePointPiecewise_distSpec
#print axioms MinimumComplement.twp_index
#print axioms MinimumComplement.twp_binomialBody
#print axioms MinimumComplement.binomial_expectation
#print axioms MinimumComplement.initial_bias

end

end ExactFactoriesReview027

#audit_dist_spec SampLib.MinimumComplement.minimumComplement_distSpec for Occil.FactoryExtra.minimumComplement
#audit_dist_spec SampLib.MinimumComplement.minimumHalf_distSpec for Occil.FactoryExtra.minimumHalf
#audit_dist_spec SampLib.MinimumComplement.threePointPiecewise_distSpec for Occil.FactoryExtra.threePointPiecewise
