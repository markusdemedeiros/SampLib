import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Series

/-! # Conditional mixtures

A fresh parameter is followed by its conditional coin. The target law is the
integral of that probability kernel against the parameter law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.IntegralMixture

noncomputable section

section mathematics

open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Integrate a conditional Boolean law against the parameter distribution. -/
def law (μ : Measure α) (κ : α → Measure Bool) : Measure Bool := μ.bind κ

theorem law_probability (μ : Measure α) [IsProbabilityMeasure μ] (κ : α → Measure Bool)
    [∀ x, IsProbabilityMeasure (κ x)] (hκ : Measurable κ) :
    IsProbabilityMeasure (law μ κ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- The tower identity accounts for arbitrary, possibly infinite, credits. -/
theorem expectation (μ : Measure α) (κ : α → Measure Bool) (hκ : Measurable κ)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ x, (∫⁻ b, F b ∂κ x) ∂μ = ∫⁻ b, F b ∂law μ κ := by
  rw [law, Measure.lintegral_bind hκ.aemeasurable (measurable_of_countable F).aemeasurable]

end mathematics

section specification

open MeasureTheory (Measure IsProbabilityMeasure)
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- Sample the parameter, then invoke its conditional distribution specification. -/
theorem twp_integralMixture (E : CoPset) (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : α → Measure Bool) [∀ x, IsProbabilityMeasure (κ x)] (hκ : Measurable κ)
    (encode : α → Val rT) (parameter factory : Val rT)
    (hparameter : IsDistSpec (GF := GF) E pl(&parameter.fst #()) μ encode)
    (hfactory : ∀ x, IsDistSpec (GF := GF) E
      pl(&factory.fst &(encode x).fst #()) (κ x) Val.bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law μ κ) -∗
      tglWp E pl(&Occil.FactoryExtra.integralMixture &parameter.fst &factory.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&parameter.fst #())
  isimp only [← expectation μ κ hκ F] at Hcredit
  iapply (hparameter.wp (fun x => ∫⁻ b, F b ∂κ x)
    ((Measure.measurable_lintegral (measurable_of_countable F)).comp hκ) _) $$ Hcredit
  iintro %x Hcredit
  twp_pures
  iapply (hfactory x).spec F (measurable_of_countable F) $$ Hcredit

/-- Typed conditional-mixture specification over any measurable parameter space. -/
theorem integralMixture_distSpec (E : CoPset) (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : α → Measure Bool) [∀ x, IsProbabilityMeasure (κ x)] (hκ : Measurable κ)
    (encode : α → Val rT) (parameter factory : Val rT)
    (hparameter : IsDistSpec (GF := GF) E pl(&parameter.fst #()) μ encode)
    (hfactory : ∀ x, IsDistSpec (GF := GF) E
      pl(&factory.fst &(encode x).fst #()) (κ x) Val.bool) :
    let := law_probability μ κ hκ
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.integralMixture &parameter.fst &factory.fst #())
      (law μ κ) Val.bool := by
  let := law_probability μ κ hκ
  exact ⟨fun F _ => wand_entails
    (twp_integralMixture E μ κ hκ encode parameter factory hparameter hfactory F)⟩

end specification

end

end SampLib.IntegralMixture
