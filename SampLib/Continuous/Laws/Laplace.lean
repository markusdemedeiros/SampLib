module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.Prod
public import SampLib.Bernoulli.Laws.VonNeumann

@[expose] public section

/-! # Laplace law as a unit exponential with a fair sign

The sign is independent of the magnitude, so the law is invariant under reflection.
-/

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

end

end SampLib.Laplace
