import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.TrigonometricSeriesFactories
import SampLib.Bernoulli.ArcsineFactories

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

namespace ExactFactoriesReview023

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
  frame (TrigonometricSeriesFactories.cosineSqrt_distSpec E p coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec E p coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArcsineFactories.arcsineHalf_distSpec E p coin hcoin) F I

example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 6*b)
    (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TrigonometricSeriesFactories.sincSqrtScaled_distSpec E a b ha hb hab p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TrigonometricSeriesFactories.sincSqrtScaled_distSpec
    E 6 1 (by decide) (by decide) (by decide) 1 coin hcoin) F I

example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 6*b)
    (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TrigonometricSeriesFactories.sincScaled_distSpec E a b ha hb hab p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TrigonometricSeriesFactories.sincScaled_distSpec
    E 6 1 (by decide) (by decide) (by decide) 1 coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (TrigonometricSeriesFactories.cosineSqrt_distSpec E 0 coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArcsineFactories.arcsineHalf_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArcsineFactories.arcsineHalf_distSpec E 1 coin hcoin) F I

example : (ArcsineFactoryParameters.bias 1 : ℝ) = Real.pi/2-1 := by
  rw [ArcsineFactoryParameters.bias_coe]
  norm_num

example : (ArcsineFactories.halfBias 1 : ℝ) = Real.pi/4 := by
  rw [ArcsineFactories.halfBias_coe, show ((1 : unitInterval) : ℝ) = 1 from rfl,
    Real.arcsin_one]
  ring

example : RealCoin.credit (ArcsineFactoryParameters.bias 0)
    (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ArcsineFactoryParameters.bias_coe]

example : RealCoin.credit (ArcsineFactories.halfBias 0)
    (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ArcsineFactories.halfBias_coe]

example : RealCoin.credit
    (AlternatingSeries.meanBias TrigonometricFactoryParameters.cosine 0)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, TrigonometricFactoryParameters.cosine_mean_coe]

#print axioms ArcsineFactoryParameters.bias_coe
#print axioms ArcsineFactories.halfBias_coe
#print axioms ArcsineFactorySeries.generating
#print axioms ArcsineFactorySeries.integrated_series
#print axioms AlternatingSeries.continuous_meanBias
#print axioms TrigonometricFactoryParameters.sinc_scaled_mean_coe

end

end ExactFactoriesReview023

#print axioms SampLib.TrigonometricSeriesFactories.cosineSqrt_distSpec
#audit_dist_spec SampLib.TrigonometricSeriesFactories.cosineSqrt_distSpec for Occil.FactoryExtra.cosineSqrt
#print axioms SampLib.TrigonometricSeriesFactories.sincSqrtScaled_distSpec
#audit_dist_spec SampLib.TrigonometricSeriesFactories.sincSqrtScaled_distSpec for Occil.FactoryExtra.sincSqrtScaled
#print axioms SampLib.TrigonometricSeriesFactories.sincScaled_distSpec
#audit_dist_spec SampLib.TrigonometricSeriesFactories.sincScaled_distSpec for Occil.FactoryExtra.sincScaled
#print axioms SampLib.ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec
#audit_dist_spec SampLib.ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec for Occil.FactoryExtra.arcsinePlusSqrtMinusOne
#print axioms SampLib.ArcsineFactories.arcsineHalf_distSpec
#audit_dist_spec SampLib.ArcsineFactories.arcsineHalf_distSpec for Occil.FactoryExtra.arcsineHalf
