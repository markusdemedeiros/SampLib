import SampLib
import SampLib.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Samplers.AlternatingSeries

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

namespace ExactFactoriesReview021

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

example (E : CoPset) (a : AlternatingSeries.Parameters) (raw : ℕ → FactoryFractions.Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (p : unitInterval)
    (coin coefficient : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcoefficient : ∀ n : ℕ, ⊢ tglWp E pl(&coefficient.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AlternatingSeries.alternatingSeries_distSpec E a raw hraw p
    coin coefficient hcoin hcoefficient) F I

private def harmonic : AlternatingSeries.Parameters where
  coefficient n := 1 / (n + 1)
  nonnegative n := by positivity
  decreasing := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  initial := by norm_num
  vanishes := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private def raw (n : ℕ) : FactoryFractions.Fraction := ⟨1, n + 1, by omega⟩

private theorem raw_value (n : ℕ) : (raw n).value = harmonic.coefficient n := by
  simp [raw, FactoryFractions.Fraction.value, harmonic, Rat.mkRat_eq_div]

private def harmonicCode {rT : Type} : Val rT :=
  ⟨pl(fun n, (#1, n + #1)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem harmonicCode_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(harmonicCode (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  simp [raw, FactoryFractions.Fraction.encode, Nat.cast_add, Nat.cast_one]

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (AlternatingSeries.alternatingSeries_distSpec E harmonic raw raw_value 1
    coin harmonicCode hcoin (harmonicCode_spec E)) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (AlternatingSeries.alternatingSeries_distSpec E harmonic raw raw_value 0
    coin harmonicCode hcoin (harmonicCode_spec E)) (fun b => if b then 0 else ∞) I

private theorem harmonic_zero : (AlternatingSeries.meanBias harmonic 0 : ℝ) = 1 := by
  apply AlternatingSeries.mean_eq_of_hasSum
  convert (hasSum_ite_eq 0 (1 : ℝ)) using 1
  funext n
  by_cases hn : n = 0 <;>
    simp [AlternatingEnclosure.sign_eq, AlternatingSeries.value, harmonic, hn]

example : RealCoin.credit (AlternatingSeries.meanBias harmonic 0)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, harmonic_zero]

#print axioms AlternatingSeries.alternatingSeries_distSpec
#print axioms AlternatingSeries.expectation
#print axioms AlternatingSeries.exists_horizon
#print axioms AlternatingSeries.weighted_partialSum_tendsto
#print axioms AlternatingSeries.mean_eq_of_tendsto
#print axioms AlternatingSeries.mean_eq_of_hasSum

end

end ExactFactoriesReview021

#audit_dist_spec SampLib.AlternatingSeries.alternatingSeries_distSpec for Occil.FactoryExtra.alternatingSeries
