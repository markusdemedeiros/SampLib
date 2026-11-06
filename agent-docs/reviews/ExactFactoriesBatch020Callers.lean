import SampLib
import SampLib.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Samplers.LogRatioFactories

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

namespace ExactFactoriesReview020

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

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogRatioFactories.complementOverLogInverse_distSpec E p hp coin hcoin) F I

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogRatioFactories.pOverLogInverseComplement_distSpec E p hp coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (LogRatioFactories.complementOverLogInverse_distSpec E 1 (by norm_num) coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (LogRatioFactories.pOverLogInverseComplement_distSpec E 0 (by norm_num) coin hcoin)
    (fun b => if b then 0 else ∞) I

theorem conditional_frame (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformBag.owns l q ∗ ↯ (LatentBernoulli.credit q
      (fun u => FractionalPower.powerBias p (φ u)) G)) ∗ I) ⊢
      tglWp E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
        (fun v : Val rT => iprop(∃ (b : Bool) (q' : List Bool),
          ⌜v = Val.bool b ∧ q <+: q'⌝ ∗ UniformBag.owns l q' ∗
          ↯ (DyadicPosterior.credit q' (G b)) ∗ I)) := by
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  iapply ((LatentPower.twoCoinPower_coinSpec E p hp φ base exponent l hbase hexponent).wp
    q G hG _) $$ Hbag Hcredit
  iintro %b %q' %hpq Hbag Hcredit
  iexists b, q'
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hpq⟩

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (I : IProp GF) :=
  conditional_frame E p hp φ base exponent l hbase hexponent q
    (fun b u => if b then ENNReal.ofReal u else ∞)
    (by intro b; cases b <;> fun_prop) I

example : RealCoin.credit (LogRatioFactories.complementBias 1 (by norm_num))
    (fun b => if b then 0 else ∞) = 0 := by
  simp [LogRatioFactories.complementBias, LogarithmicMean.bias, RealCoin.credit, RealCoin.pmf]

example : RealCoin.credit (LogRatioFactories.overLogBias 0 (by norm_num))
    (fun b => if b then 0 else ∞) = 0 := by
  simp [LogRatioFactories.overLogBias, LogarithmicMean.bias, RealCoin.credit, RealCoin.pmf]

private def observedProgram (base exponent : Val rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) (.app exponent.fst (.lit .unit))))
    pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())

theorem observe_again (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (H : Bool → Bool → ℝ → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (I : IProp GF) :
    iprop((UniformBag.owns l q ∗ ↯ (LatentBernoulli.credit q
      (fun u => FractionalPower.powerBias p (φ u))
      (fun b u => LatentBernoulli.kernel φ (H b) u))) ∗ I) ⊢
      tglWp E (observedProgram base exponent)
        (fun v : Val rT => iprop(∃ (b c : Bool) (q' : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.bool c) ∧ q <+: q'⌝ ∗
          UniformBag.owns l q' ∗ ↯ (DyadicPosterior.credit q' (H b c)) ∗ I)) := by
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  unfold observedProgram
  twp_bind pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
  iapply ((LatentPower.twoCoinPower_coinSpec E p hp φ base exponent l hbase hexponent).wp q
    (fun b u => LatentBernoulli.kernel φ (H b) u)
    (fun b => LatentBernoulli.measurable_kernel hexponent.measurable_bias (hH b)) _)
    $$ Hbag Hcredit
  iintro %b %q' %hqq' Hbag Hcredit
  twp_pure
  twp_bind pl(&exponent.fst #())
  have hfold : DyadicPosterior.credit q'
      (fun u => LatentBernoulli.kernel φ (H b) u) = LatentBernoulli.credit q' φ (H b) := rfl
  isimp only [hfold] at Hcredit
  iapply (hexponent.wp q' (H b) (hH b) _) $$ Hbag Hcredit
  iintro %c %q'' %hq'q'' Hbag Hcredit
  twp_pures
  twp_value
  imodintro
  iexists b, c, q''
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hqq'.trans hq'q''⟩

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (I : IProp GF) :=
  observe_again E p hp φ base exponent l hbase hexponent q
    (fun b c u => if b && c then ENNReal.ofReal u else ∞)
    (by intro b c; cases b <;> cases c <;> fun_prop) I

example (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (LogRatioFactories.complementBias p hp : ℝ) =
      if (p : ℝ) = 1 then 1 else (1 - (p : ℝ)) / Real.log (1 / (p : ℝ)) :=
  LogRatioFactories.complementBias_coe p hp

example (p : unitInterval) (hp : (p : ℝ) < 1) :
    (LogRatioFactories.overLogBias p hp : ℝ) =
      if (p : ℝ) = 0 then 1 else (p : ℝ) / Real.log (1 / (1 - (p : ℝ))) :=
  LogRatioFactories.overLogBias_coe p hp

#print axioms LogRatioFactories.complementOverLogInverse_distSpec
#print axioms LogRatioFactories.pOverLogInverseComplement_distSpec
#print axioms LatentPower.twoCoinPower_coinSpec
#print axioms LogarithmicMean.expectation
#print axioms PowerIntegral.integral_const_power

end

end ExactFactoriesReview020

#audit_dist_spec SampLib.LogRatioFactories.complementOverLogInverse_distSpec for Occil.FactoryExtra.complementOverLogInverse
#audit_dist_spec SampLib.LogRatioFactories.pOverLogInverseComplement_distSpec for Occil.FactoryExtra.pOverLogInverseComplement
