import SampLib.Continuous.Exponential
import SampLib.Uniform.FairCoin

/-! # Laplace sampling by an independent exponential magnitude and fair sign -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Laplace

noncomputable section

section mathematics

open MeasureTheory

private instance : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one

/-- Standard Laplace law, as an independent fair sign times a unit exponential. -/
def law : Measure ℝ :=
  ((ProbabilityTheory.expMeasure 1).prod (RealCoin.law VonNeumann.fairBias)).map
    (fun z : ℝ × Bool => if z.2 then z.1 else -z.1)

private theorem measurable_sign :
    Measurable (fun z : ℝ × Bool => if z.2 then z.1 else -z.1) :=
  Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    measurable_fst measurable_fst.neg

instance : IsProbabilityMeasure law := by
  unfold law
  infer_instance

/-- Credit after observing the exponential magnitude. -/
def credit (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ b, F (if b then x else -x) ∂RealCoin.law VonNeumann.fairBias

theorem measurable_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit F) :=
  (hF.comp measurable_sign).lintegral_prod_right'

/-- Independent sign and magnitude give the successive conditional expectations. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit F x ∂ProbabilityTheory.expMeasure 1 = ∫⁻ z, F z ∂law := by
  rw [law, lintegral_map hF measurable_sign]
  exact (lintegral_prod _ (hF.comp measurable_sign).aemeasurable).symm

/-- Reflecting the independent fair sign leaves every measurable expectation unchanged. -/
theorem reflection (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F (-z) ∂law = ∫⁻ z, F z ∂law := by
  rw [← expectation_preservation (fun z => F (-z)) (hF.comp measurable_neg),
    ← expectation_preservation F hF]
  apply MeasureTheory.lintegral_congr
  intro x
  simp [credit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    VonNeumann.fairBias]
  norm_num only [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat, one_div]
  exact add_comm _ _

/-- The standard Laplace law is invariant under reflection. -/
@[simp] theorem map_neg : law.map (fun x => -x) = law := by
  apply MeasureTheory.Measure.ext_of_lintegral
  intro F hF
  rw [MeasureTheory.lintegral_map hF measurable_neg]
  exact reflection F hF

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE composition of exponential magnitude and a fresh fair sign. -/
theorem twp_laplace (E : CoPset)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law) -∗ tglWp E pl(&Occil.laplace #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  have hexp := Exponential.exponential_distSpec (GF := GF) E
  dsimp only [Exponential.law] at hexp
  iintro Hcredit
  twp_pure
  simp only [Exponential.exponential_closeRec, Exponential.exponential_openRec]
  twp_bind pl(&Occil.exponential #())
  isimp only [← expectation_preservation F hF] at Hcredit
  iapply (hexp.wp (credit F) (measurable_credit F hF) _) $$ Hcredit
  iintro %x Hcredit
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  isimp only [credit] at Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (fun b => F (if b then x else -x))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b <;> twp_pures <;> twp_value <;> imodintro
  · iexists (-x)
    isimp only [Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)
  · iexists x
    isimp only [ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed standard Laplace specification. -/
theorem laplace_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.laplace #()) law Val.real where
  spec F hF := wand_entails (twp_laplace E F hF)

end specification

end

end SampLib.Laplace
