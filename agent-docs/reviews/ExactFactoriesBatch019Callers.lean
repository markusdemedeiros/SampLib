import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.AlternatingPermutation

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

namespace ExactFactoriesReview019

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformReal ℝ] in
theorem frame {E : CoPset} {e : Exp ℝ} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (odd : Bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AlternatingPermutation.alternatingPermutation_distSpec E p hp coin hcoin odd) F I

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AlternatingPermutation.complementOverCosine_distSpec E p hp coin hcoin) F I

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AlternatingPermutation.complementTimesTangent_distSpec E p hp coin hcoin) F I

example (E : CoPset) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (AlternatingPermutation.complementOverCosine_distSpec E 0 (by norm_num) coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (AlternatingPermutation.complementTimesTangent_distSpec E 0 (by norm_num) coin hcoin)
    (fun b => if b then ∞ else 0) I

example : (AlternatingPermutationMixture.bias 0 false : ℝ) = 1 := by
  rw [AlternatingPermutationMixture.bias_coe 0 (by norm_num)]
  norm_num

example : (AlternatingPermutationMixture.bias 0 true : ℝ) = 0 := by
  rw [AlternatingPermutationMixture.bias_coe 0 (by norm_num)]
  norm_num

example : RealCoin.credit (AlternatingPermutationMixture.bias 0 false)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, AlternatingPermutationMixture.bias_coe 0 (by norm_num)]

example : RealCoin.credit (AlternatingPermutationMixture.bias 0 true)
    (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, AlternatingPermutationMixture.bias_coe 0 (by norm_num)]

#print axioms AlternatingPermutation.alternatingPermutation_distSpec
#print axioms AlternatingPermutation.complementOverCosine_distSpec
#print axioms AlternatingPermutation.complementTimesTangent_distSpec
#print axioms AlternatingPermutationMixture.expectation
#print axioms AlternatingPermutationMixture.bias_coe
#print axioms AlternatingPermutationLaw.hasSum_eventMass

end

end ExactFactoriesReview019

#audit_dist_spec SampLib.AlternatingPermutation.alternatingPermutation_distSpec for Occil.FactoryExtra.alternatingPermutation
#audit_dist_spec SampLib.AlternatingPermutation.complementOverCosine_distSpec for Occil.FactoryExtra.complementOverCosine
#audit_dist_spec SampLib.AlternatingPermutation.complementTimesTangent_distSpec for Occil.FactoryExtra.complementTimesTangent
