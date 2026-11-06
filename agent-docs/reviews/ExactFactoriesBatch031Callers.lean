import SampLib
import SampLib.Core.OwnedDistSpec
import Lean.Elab.Command
import SampLib.Bernoulli.EnvelopeFactory
import SampLib.Uniform.FairCoin
import SampLib.Bernoulli.Laws.BernoulliEndpoints

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

set_option maxHeartbeats 400000

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview031

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
open EnvelopeFactory FactoryFractions

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- A Bernoulli spec preserves an arbitrary framed resource and arbitrary ENNReal credits. -/
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

/-! ## Abstract public interfaces, framed -/

example (E : CoPset) (p : unitInterval) (a : Parameters p) (r : a.toCoefficients.Realization)
    (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (envelopeFactoryDegrees_distSpec E p a r coin bounds next hcoin hbounds hnext) F I

example (E : CoPset) (p : unitInterval) (a : Parameters p) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (envelopeFactory_distSpec E p a r ha coin bounds hcoin hbounds) F I

/-- Convergence is needed only at the input bias: any coefficient contract plus a limit at `p`. -/
example (E : CoPset) (p τ : unitInterval) (c : Coefficients)
    (hlo : Filter.Tendsto (fun t => c.lowerMean t p) Filter.atTop (nhds (τ : ℝ)))
    (hhi : Filter.Tendsto (fun t => c.upperMean t p) Filter.atTop (nhds (τ : ℝ)))
    (r : c.Realization) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E c r bounds) (hnext : NextSpec (GF := GF) E c next) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #()) (RealCoin.law τ) Val.bool :=
  envelopeFactoryDegrees_distSpec E p ⟨c, τ, hlo, hhi⟩ r coin bounds next hcoin hbounds hnext

private def fair : Val rT := ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩

/-- Composition with the verified fair coin, general degrees, framed. -/
example (E : CoPset) (a : Parameters VonNeumann.fairBias) (r : a.toCoefficients.Realization)
    (bounds next : Val rT) (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law a.target) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &Occil.fairCoin &bounds.fst &next.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (envelopeFactoryDegrees_distSpec E VonNeumann.fairBias a r fair bounds next
    (FairCoin.fairCoin_distSpec E) hbounds hnext) F I

/-- Composition with the verified fair coin, consecutive wrapper, framed. -/
example (E : CoPset) (a : Parameters VonNeumann.fairBias) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (bounds : Val rT)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law a.target) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactory &Occil.fairCoin &bounds.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (envelopeFactory_distSpec E VonNeumann.fairBias a r ha fair bounds
    (FairCoin.fairCoin_distSpec E) hbounds) F I

/-- Bias 0 with target 0: infinite credit on the null `true` outcome costs nothing. -/
example (E : CoPset) (a : Parameters 0) (r : a.toCoefficients.Realization)
    (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (hz : a.target = 0) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗
        ↯ (if b then ∞ else 0) ∗ I)) := by
  have h := frame (GF := GF) (envelopeFactoryDegrees_distSpec E 0 a r coin bounds next hcoin
    hbounds hnext) (fun b => if b then ∞ else 0) I
  rw [RealCoin.lintegral_law, hz, RealCoin.credit_zero] at h
  exact h

/-- Bias 1 with target 1 (consecutive wrapper): infinite credit on the null `false` outcome. -/
example (E : CoPset) (a : Parameters 1) (r : a.toCoefficients.Realization)
    (ha : ∀ t, a.degree t = t) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hz : a.target = 1) (I : IProp GF) :
    ⊢ ↯ 0 ∗ I -∗ tglWp E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗
        ↯ (if b then 0 else ∞) ∗ I)) := by
  have h := frame (GF := GF) (envelopeFactory_distSpec E 1 a r ha coin bounds hcoin hbounds)
    (fun b => if b then 0 else ∞) I
  rw [RealCoin.lintegral_law, hz, RealCoin.credit_one] at h
  exact h

/-- Endpoint input bias with an arbitrary target and infinite credit on both outcomes. -/
example (E : CoPset) (a : Parameters 0) (r : a.toCoefficients.Realization)
    (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (I : IProp GF) :=
  frame (GF := GF) (envelopeFactoryDegrees_distSpec E 0 a r coin bounds next hcoin hbounds hnext)
    (fun _ => ∞) I

#print axioms SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec
#print axioms SampLib.EnvelopeFactory.envelopeFactory_distSpec
#print axioms SampLib.EnvelopeFactory.twp_envelopeFactoryDegrees
#print axioms SampLib.EnvelopeFactory.Parameters.exists_horizon
#print axioms SampLib.EnvelopeFactory.Coefficients.expectation

#audit_dist_spec SampLib.EnvelopeFactory.envelopeFactoryDegrees_distSpec for
  Occil.FactoryExtra.envelopeFactoryDegrees
#audit_dist_spec SampLib.EnvelopeFactory.envelopeFactory_distSpec for
  Occil.FactoryExtra.envelopeFactory

end

end ExactFactoriesReview031
