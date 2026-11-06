import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Constants.ErfRatio
import SampLib.Constants.LowerGammaIntegerRatio

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

namespace ExactFactoriesReview026

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

example (E : CoPset) (x : unitInterval) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ErfRatio.erfRatio_distSpec E x) F I

example (E : CoPset) (m : ℕ) (hm : 0 < m) (x : unitInterval)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E m hm x) F I

example (E : CoPset) (I : IProp GF) :=
  frame (ErfRatio.erfRatio_distSpec E 0) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (ErfRatio.erfRatio_distSpec E 1) (fun b => if b then 0 else ∞) I

example (E : CoPset) (I : IProp GF) :=
  frame (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E 1 (by decide) 0)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (m : ℕ) (hm : 0 < m) (I : IProp GF) :=
  frame (LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec E m hm 1)
    (fun b => if b then 0 else ∞) I

example (x : unitInterval) : (ErfRatio.bias x : ℝ) =
    ErrorFunctionKernel.erf x / ErrorFunctionKernel.erf 1 := ErfRatio.bias_coe x x.2

example (m : ℕ) (_hm : 0 < m) (x : unitInterval) :
    (LowerGammaIntegerRatio.bias (m-1) x : ℝ) =
      IntegerGammaKernel.lowerGamma (m-1) x / IntegerGammaKernel.lowerGamma (m-1) 1 :=
  LowerGammaIntegerRatio.bias_coe (m-1) x x.2

omit [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ] in
private theorem erf_denominator : ErrorFunctionKernel.erf 1 ≠ 0 := by
  have hm : AcceptedProposal.mass LawfulProbLangℝ.unifUnit SquaredDecreasing.decay ≠ 0 :=
    ThresholdRejection.mass_ne_zero _ _ SquaredDecreasing.measurable_decay
      (fun _ => Real.exp_pos _)
  have hi : ErrorFunctionKernel.integral 1 ≠ 0 := by
    intro h
    apply hm
    rw [ErrorFunctionKernel.mass_eq, h, ENNReal.ofReal_zero]
  exact mul_ne_zero (by positivity) hi

omit [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ] in
private theorem gamma_denominator (n : ℕ) : IntegerGammaKernel.lowerGamma n 1 ≠ 0 := by
  have hm : AcceptedProposal.mass (MaximumUniform.law n) IntegerGammaKernel.acceptance ≠ 0 :=
    ThresholdRejection.mass_ne_zero _ _ (ExponentialFactory.measurable_decay 1)
      (fun _ => Real.exp_pos _)
  intro h
  apply hm
  rw [IntegerGammaKernel.mass_eq, h, mul_zero, ENNReal.ofReal_zero]

example : (ErfRatio.bias 0 : ℝ) = 0 := by
  rw [ErfRatio.bias_coe 0 (by norm_num)]
  simp [ErrorFunctionKernel.erf, ErrorFunctionKernel.integral]

example : (ErfRatio.bias 1 : ℝ) = 1 := by
  rw [ErfRatio.bias_coe 1 (by norm_num), div_self erf_denominator]

example (n : ℕ) : (LowerGammaIntegerRatio.bias n 0 : ℝ) = 0 := by
  rw [LowerGammaIntegerRatio.bias_coe n 0 (by norm_num)]
  simp [IntegerGammaKernel.lowerGamma]

example (n : ℕ) : (LowerGammaIntegerRatio.bias n 1 : ℝ) = 1 := by
  rw [LowerGammaIntegerRatio.bias_coe n 1 (by norm_num), div_self (gamma_denominator n)]

example : RealCoin.credit (ErfRatio.bias 0) (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ErfRatio.bias_coe 0 (by norm_num),
    ErrorFunctionKernel.erf, ErrorFunctionKernel.integral]

example (n : ℕ) : RealCoin.credit (LowerGammaIntegerRatio.bias n 1)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, LowerGammaIntegerRatio.bias_coe n 1 (by norm_num),
    gamma_denominator]

#print axioms ErfRatio.erfRatio_distSpec
#print axioms ErfRatio.bias_coe
#print axioms LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec
#print axioms LowerGammaIntegerRatio.bias_coe
#print axioms SquaredDecreasingChain.twp_chain
#print axioms SquaredDecreasingChain.expectation
#print axioms IntegerGammaKernel.weighted_integral
#print axioms ThresholdRejection.expectation_preservation

end

end ExactFactoriesReview026

#audit_dist_spec SampLib.ErfRatio.erfRatio_distSpec for Occil.Constants.erfRatio
#audit_dist_spec SampLib.LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec for Occil.Constants.lowerGammaIntegerRatio
