import SampLib
import SampLib.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Samplers.RationalFunction

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

namespace ExactFactoriesReview030

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

open FactoryFractions PolynomialFactory

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ []) (H : ∃ n, Admissible xs n)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (polynomial_distSpec E p coin hcoin xs hxs H) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs ys : List Fraction) (hxs : xs ≠ []) (hys : ys ≠ [])
    (Hx : ∃ n, Admissible xs n) (Hy : ∃ n, Admissible ys n)
    (hpos : 0 < value xs p + value ys p) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (rationalFunction_distSpec E p coin hcoin xs ys hxs hys Hx Hy hpos) F I

private def elevated : List Fraction :=
  [⟨21, 70, by decide⟩, ⟨-7, 7, by decide⟩, ⟨5, 5, by decide⟩]

private theorem nonempty : elevated ≠ [] := by simp [elevated]

private theorem admissible_five : Admissible elevated 5 := by
  constructor
  · norm_num [degree, elevated]
  · intro k hk
    interval_cases k <;>
      norm_num [coefficient, input, elevated, Fraction.value, Finset.sum_range_succ, Nat.choose]

example : coefficient elevated 2 1 = -(1/5 : ℚ) := by
  norm_num [coefficient, input, elevated, Fraction.value, Finset.sum_range_succ, Nat.choose]

example : coefficient elevated 3 1 = -(1/30 : ℚ) := by
  norm_num [coefficient, input, elevated, Fraction.value, Finset.sum_range_succ, Nat.choose]

example : coefficient elevated 4 2 = -(1/30 : ℚ) := by
  norm_num [coefficient, input, elevated, Fraction.value, Finset.sum_range_succ, Nat.choose]

example : coefficient elevated 5 2 = (0 : ℚ) := by
  norm_num [coefficient, input, elevated, Fraction.value, Finset.sum_range_succ, Nat.choose]

private theorem value_form (x : ℝ) : value elevated x = (x-1/2)^2+1/20 := by
  norm_num [value, PolynomialBernstein.value, degree, input, elevated, Fraction.value,
    Finset.sum_range_succ]
  ring

private theorem strict : ∀ x : unitInterval, value elevated x ∈ Set.Ioo 0 1 := by
  intro x
  rw [value_form]
  constructor
  · nlinarith [sq_nonneg ((x : ℝ)-1/2)]
  · nlinarith [mul_nonneg x.2.1 (sub_nonneg.mpr x.2.2)]

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (polynomial_distSpec E p coin hcoin elevated nonempty ⟨5, admissible_five⟩) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (polynomial_strict_distSpec E p coin hcoin elevated nonempty strict) F I

example : value elevated (0 : unitInterval) = 3/10 := by rw [value_form]; norm_num
example : value elevated (1 : unitInterval) = 3/10 := by rw [value_form]; norm_num

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (rationalFunction_distSpec E p coin hcoin elevated elevated nonempty nonempty
    ⟨5, admissible_five⟩ ⟨5, admissible_five⟩ (by
      rw [value_form]
      nlinarith [sq_nonneg ((p : ℝ)-1/2)])) F I

private def constant (q : ℚ) : List Fraction := [Fraction.ofRat q]

private theorem constant_nonempty (q : ℚ) : constant q ≠ [] := by simp [constant]

private theorem constant_admissible (q : ℚ) (hq : q ∈ Set.Icc 0 1) :
    Admissible (constant q) 0 := by
  constructor
  · simp [degree, constant]
  · intro k hk
    have h : k=0 := by omega
    subst k
    simpa [coefficient, input, constant, Finset.sum_range_succ] using hq

private theorem constant_value (q : ℚ) (x : ℝ) : value (constant q) x = (q : ℝ) := by
  simp [value, PolynomialBernstein.value, degree, input, constant]

private theorem Hzero : ∃ n, Admissible (constant 0) n :=
  ⟨0, constant_admissible 0 (by norm_num)⟩

private theorem Hone : ∃ n, Admissible (constant 1) n :=
  ⟨0, constant_admissible 1 (by norm_num)⟩

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (I : IProp GF) :=
  frame (polynomial_distSpec E p coin hcoin (constant 0) (constant_nonempty 0) Hzero)
    (fun b => if b then ∞ else 0) I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (I : IProp GF) :=
  frame (rationalFunction_distSpec E p coin hcoin (constant 1) (constant 0)
    (constant_nonempty 1) (constant_nonempty 0) Hone Hzero
    (by rw [constant_value, constant_value]; norm_num)) (fun b => if b then 0 else ∞) I

example (p : unitInterval) :
    RealCoin.credit (bias (constant 0) (constant_nonempty 0) Hzero p)
      (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, constant_value]

#print axioms polynomial_distSpec
#print axioms polynomial_strict_distSpec
#print axioms rationalFunction_distSpec
#print axioms twp_polynomial
#print axioms exists_admissible
#print axioms PolynomialBernstein.evaluation
#print axioms PolynomialBernstein.exists_admissible_degree

end

end ExactFactoriesReview030

#audit_dist_spec SampLib.PolynomialFactory.polynomial_distSpec for Occil.FactoryExtra.polynomial
#audit_dist_spec SampLib.PolynomialFactory.rationalFunction_distSpec for Occil.FactoryExtra.rationalFunction
