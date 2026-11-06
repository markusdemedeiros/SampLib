import SampLib.Templates

/-! # Distribution specifications with almost-sure support

Impossible outputs receive infinite credit, allowing callers to use support facts
without exposing the credit argument at each call site.
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace SampLib.IsDistSpec

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
variable {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}
local bi (IProp GF)

/-- Use an almost-sure support fact together with the ordinary continuation credit. -/
theorem wp_supported (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hs : ∀ᵐ x ∂μ, P x)
    (F : α → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) -∗
      (∀ x : α, ⌜P x⌝ -∗ ↯ (F x) -∗ Φ (encode x)) -∗ tglWp E e Φ := by
  classical
  let K := fun x => if P x then F x else ∞
  have hK : Measurable K := Measurable.ite hP hF measurable_const
  have hbudget : ∫⁻ x, K x ∂μ = ∫⁻ x, F x ∂μ :=
    MeasureTheory.lintegral_congr_ae (hs.mono fun x hx => ite_eq_left hx)
  iintro Hcredit Hcont
  isimp only [← hbudget] at Hcredit
  iapply (h.wp K hK Φ) $$ Hcredit
  iintro %x Hcredit
  by_cases hx : P x
  · isimp only [K, ite_eq_left hx] at Hcredit
    iapply Hcont $$ %x %hx Hcredit
  · isimp only [K, ite_eq_right hx] at Hcredit
    ihave %hbad := ErrorCredit.valid $$ Hcredit
    exact (not_lt_of_ge le_top hbad).elim

end

end SampLib.IsDistSpec
