import SampLib.Discrete.MultivariatePoisson
import SampLib.Discrete.LogUniform
import SampLib.Core.Syntax.ClosedExp
import Metrology.Iris.LocalBI

/-! Independent shared-count, logarithmic-bucket and syntax clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section closedExpressions

open SampLib

private def identityExp {rT : Type _} : Exp rT := .lam (.bvar 0)

private instance {rT : Type _} : ClosedExp (identityExp : Exp rT) where
  lc := by is_lc
  fv := by simp [identityExp, Exp.fv]

example {rT : Type _} (k l : ℕ) (x y : Var) (e : Exp rT) :
    Exp.closeRec k x (Exp.openRec l e (Exp.closeRec k y identityExp)) = identityExp := by
  simp only [ClosedExp.closeRec, ClosedExp.openRec]

example {rT : Type _} (x : Var) : ¬ClosedExp (.fvar x : Exp rT) := by
  intro h
  have hf := h.fv
  simp [Exp.fv] at hf

end closedExpressions

section mathematics

open MeasureTheory Measure SampLib

private def zeroRate : MultivariatePoisson.Rate := ⟨(0, 1), by decide⟩

example (r : ℝ≥0) : MultivariatePoisson.law r [] = dirac [] := by
  apply Measure.ext_of_singleton
  intro ns
  rw [MultivariatePoisson.law, Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  simp [MultivariatePoisson.components]

example (shared : ℕ) : MultivariatePoisson.components shared [zeroRate, zeroRate] =
    dirac [shared, shared] := by
  simp [MultivariatePoisson.components, zeroRate, PoissonRational.rate,
    Distributions.poissonMeasure_zero, Measure.dirac_prod_dirac,
    Measure.map_dirac' (measurable_of_countable _)]

example (r : ℝ≥0) (rs : List MultivariatePoisson.Rate) :
    (∫⁻ _ns, (∞ : ℝ≥0∞) ∂MultivariatePoisson.law r rs) = ∞ := by simp

example : LogUniform.lastLevel 7 2 = 3 := by decide
example : LogUniform.lastLevel 8 2 = 4 := by decide
example : LogUniform.lower 7 2 3 = 4 ∧ LogUniform.upper 7 2 3 = 7 := by decide
example : LogUniform.lower 8 2 4 = 8 ∧ LogUniform.upper 8 2 4 = 8 := by decide
example (base : ℕ) : LogUniform.law 0 base = dirac 0 := LogUniform.law_zero base

example : LogUniform.law 8 2 {8} = (1 : ℝ≥0∞) / 5 := by
  rw [← lintegral_indicator_one (measurableSet_singleton (8 : ℤ)), LogUniform.lintegral_law,
    show LogUniform.lastLevel 8 2 = 4 by decide]
  norm_num [Finset.sum_range_succ, LogUniform.bucket, LogUniform.lower, LogUniform.upper]
  simp_rw [← RndIntRange.expectation, RndInt.expectation]
  norm_num [Finset.sum_range_succ, Set.indicator]

example (maximum base : ℕ) : (∫⁻ _z, (∞ : ℝ≥0∞) ∂LogUniform.law maximum base) = ∞ := by
  simp

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem frame {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial


example (E : CoPset) (x y : ℕ) (hy : 0 < y) (rs : List MultivariatePoisson.Rate)
    (F : List ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ ns, F ns ∂MultivariatePoisson.law (PoissonRational.rate x y) rs) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.multivariatePoisson
        #int (x : ℤ) #int (y : ℤ) &(listVal MultivariatePoisson.encodeRate rs).fst)
        (fun v : Val rT => iprop(∃ ns : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int (n : ℤ)) ns⌝ ∗ ↯ (F ns) ∗ I)) :=
  frame (MultivariatePoisson.multivariatePoisson_distSpec E x y hy rs) F I

example (E : CoPset) (maximum base : ℕ) (hb : 1 < base)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂LogUniform.law maximum base) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.logUniform #int (maximum : ℤ) #int (base : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (LogUniform.logUniform_distSpec E maximum base hb) F I

#print axioms MultivariatePoisson.multivariatePoisson_distSpec
#print axioms MultivariatePoisson.expectation
#print axioms MultivariatePoisson.component_expectation
#print axioms LogUniform.logUniform_distSpec
#print axioms LogUniform.expectation
#print axioms ClosedExp.openRec
#print axioms ClosedExp.closeRec

end

end ExpansionDiscreteAudit
