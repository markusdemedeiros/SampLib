import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Constants.ZetaRelated

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

namespace ExactFactoriesReview025

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

example (E : CoPset) (k : ℕ) (hk : 2 ≤ k) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ZetaRelated.zetaRelated_distSpec E k hk) F I

example (E : CoPset) (I : IProp GF) :=
  frame (ZetaRelated.zetaRelated_distSpec E 2 (by decide)) (fun b => if b then ∞ else 0) I

example (E : CoPset) (I : IProp GF) :=
  frame (ZetaRelated.zetaRelated_distSpec E 3 (by decide)) (fun b => if b then 0 else ∞) I

example : (∫ u, (ZetaProductIntegral.product u) ^ 1 ∂ZetaProductIntegral.law 2) =
    (1 : ℝ)/4 := by rw [ZetaProductIntegral.moment]; norm_num

example : (∫ u, (ZetaProductIntegral.product u) ^ 2 ∂ZetaProductIntegral.law 3) =
    (1 : ℝ)/27 := by rw [ZetaProductIntegral.moment]; norm_num

example (k : ℕ) (hk : 2 ≤ k) : (ZetaRelated.marginalBias k : ℝ) =
    (1-(2 : ℝ)^(1-(k : ℝ))) * (riemannZeta k).re := ZetaRelated.marginalBias_coe hk

example : (ZetaRelated.marginalBias 2 : ℝ) = (riemannZeta 2).re/2 := by
  rw [ZetaRelated.marginalBias_coe (by decide)]
  norm_num
  ring

example : (ZetaRelated.marginalBias 3 : ℝ) = (3/4 : ℝ)*(riemannZeta 3).re := by
  rw [ZetaRelated.marginalBias_coe (by decide)]
  norm_num

theorem joint_frame (E : CoPset) {n : ℕ} (roots : Fin n → Loc)
    (p : Fin n → List Bool) (G : Bool → (Fin n → ℝ) → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformVector.rootsOwns roots p ∗
      ↯ (LatentReal.LatentCoin.credit (UniformVector.world n) p
        (ZetaRelated.conditionalBias n) G)) ∗ I) ⊢
      tglWp E pl(&Occil.oneDivOnePlus &(ZetaBags.productCallback roots : Val rT).fst #())
        (fun v : Val rT => iprop(
          LatentReal.LatentCoin.post (UniformVector.world n)
            (fun _ : Val rT => UniformVector.rootsOwns roots) Val.unit p G v ∗ I)) := by
  iintro ⟨⟨Hstate, Hcredit⟩, HI⟩
  isimp only [ZetaRelated.conditionalBias] at Hcredit
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply ZetaBags.twp_reciprocal E roots p G hG
    iframe Hstate Hcredit
  iintro %v Hpost
  iframe Hpost HI

example (E : CoPset) (roots : Fin 2 → Loc) (p : Fin 2 → List Bool) (I : IProp GF) :=
  joint_frame E roots p (fun b u => if b then ENNReal.ofReal (u 0 * u 1) else ∞)
    (by intro b; cases b <;> fun_prop) I

#print axioms ZetaRelated.zetaRelated_distSpec
#print axioms ZetaBags.product_coinSpec
#print axioms ZetaBags.twp_create
#print axioms ZetaRelated.marginalBias_coe
#print axioms ZetaRelated.expectation_eta
#print axioms ZetaProductIntegral.integral_eq_alternating
#print axioms ZetaProductIntegral.integral_eq_zeta

end

end ExactFactoriesReview025

#audit_dist_spec SampLib.ZetaRelated.zetaRelated_distSpec for Occil.Constants.zetaRelated
