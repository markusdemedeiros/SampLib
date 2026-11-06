import SampLib
import SampLib.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Samplers.FiniteRationalContinuedFraction

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

namespace ExactFactoriesReview016

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

example (E : CoPset) (a : ℕ → FiniteRationalContinuedFraction.Coefficient)
    (coefficient : Val rT) (depth start : ℕ) (hfinal : (a (start + depth)).last = true)
    (horacle : ∀ i, start ≤ i → i ≤ start + depth →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = FiniteRationalContinuedFraction.encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec
    E a coefficient depth start hfinal horacle) F I

example (E : CoPset) (a : ℕ → RationalContinuedFraction.Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (horacle : ∀ i, RationalContinuedFraction.Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = RationalContinuedFraction.encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (RationalContinuedFraction.rationalContinuedFraction_distSpec
    E a start coefficient horacle) F I

private def exampleCoefficients (i : ℕ) : FiniteRationalContinuedFraction.Coefficient :=
  if i = 1 then ⟨1, 1, 8, by decide, by decide, by decide, false⟩
  else ⟨1, 2, 100, by decide, by decide, by decide, true⟩

private def exampleCode {rT : Type} : Val rT :=
  ⟨pl(fun i, if i = #1 then (#1, (#1, (#8, #false)))
    else (#1, (#2, (#100, #true)))), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem exampleCode_spec (E : CoPset) (i : ℕ) :
    ⊢ tglWp E pl(&(exampleCode (rT := rT)).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v =
        FiniteRationalContinuedFraction.encodeCoefficient (exampleCoefficients i)⌝)) := by
  by_cases h : i = 1
  · subst i
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  · have hi : (i : ℤ) ≠ 1 := by exact_mod_cast h
    twp_pures
    simp only [show ((BaseLit.int (i : ℤ) : BaseLit rT) == .int 1) = false by
      simpa using hi]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [FiniteRationalContinuedFraction.encodeCoefficient, exampleCoefficients, h]

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec
    E exampleCoefficients exampleCode 1 1 (by decide)
    (fun i _ _ => exampleCode_spec E i)) F I

example : (FiniteRationalContinuedFraction.value exampleCoefficients 1 1 : ℝ) = 1 / 5 := by
  norm_num [FiniteRationalContinuedFraction.value, exampleCoefficients,
    FiniteRationalContinuedFraction.step, FiniteRationalContinuedFraction.direct, RationalCoin.bias]

example : ¬ (exampleCoefficients 1).scale ≤ (exampleCoefficients 1).numerator := by decide

#print axioms FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec
#print axioms FiniteRationalContinuedFraction.twp_rationalContinuedFraction_finite
#print axioms RationalContinuedFraction.rationalContinuedFraction_distSpec

end

end ExactFactoriesReview016

#audit_dist_spec SampLib.FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec for Occil.Constants.rationalContinuedFraction
#audit_dist_spec SampLib.RationalContinuedFraction.rationalContinuedFraction_distSpec for Occil.Constants.rationalContinuedFraction
