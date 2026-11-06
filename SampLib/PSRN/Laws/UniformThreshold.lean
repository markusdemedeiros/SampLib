import SampLib.PSRN.Support.LatentProductModel
import SampLib.Latent.LatentUniform
import SampLib.Latent.LatentCoinSpec
import SampLib.Latent.Laws.LatentBernoulli

/-! # An independent uniform threshold yields a conditional Bernoulli kernel -/

open Set MeasureTheory ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.UniformThreshold

noncomputable section

private theorem unitLaw_eq_unif : DyadicPosterior.unitLaw = LawfulProbLangℝ.unifUnit (T := ℝ) := by
  change volume.restrict (Ico (0 : ℝ) 1) = volume.restrict (Icc (0 : ℝ) 1)
  exact restrict_Ico_eq_restrict_Icc

/-- Clamping changes no comparison with a point in the unit interval. -/
private theorem threshold_clamp {u x : ℝ} (hu : u ∈ Ico 0 1) :
    u < x ↔ u < (LatentBernoulli.bias x : ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [LatentBernoulli.bias, projIcc_of_le_left zero_le_one hx]
    exact iff_of_false (not_lt.mpr (hx.trans hu.1)) (not_lt.mpr hu.1)
  · by_cases h1 : 1 ≤ x
    · simp only [LatentBernoulli.bias, projIcc_of_right_le zero_le_one h1]
      exact iff_of_true (hu.2.trans_le h1) hu.2
    · rw [LatentBernoulli.bias_coe ⟨(not_le.mp hx).le, not_le.mp h1⟩]

/-- The threshold identity permits arbitrary, including infinite, Boolean credits. -/
theorem expectation_threshold (x : ℝ) (F : Bool → ℝ≥0∞) :
    (∫⁻ u, F (decide (u < x)) ∂DyadicPosterior.unitLaw) =
      RealCoin.credit (LatentBernoulli.bias x) F := by
  have hunit : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Ico 0 1 := by
    simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
  calc
    _ = ∫⁻ u, RealCoin.uniformCredit (LatentBernoulli.bias x) F u ∂DyadicPosterior.unitLaw := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with u hu
      rw [RealCoin.uniformCredit_eq]
      simp only [← threshold_clamp hu]
    _ = _ := by rw [unitLaw_eq_unif]; exact RealCoin.lintegral_uniformCredit _ _

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Comparison continuation on the full source/uniform product world. -/
def kernel (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞) (z : ℝ × Ω) : ℝ≥0∞ :=
  G (decide (z.1 < D.value z.2)) z.2

theorem measurable_kernel (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) : Measurable (kernel D G) := by
  have heq : kernel D G = fun z => if z.1 < D.value z.2 then G true z.2 else G false z.2 := by
    funext z
    by_cases h : z.1 < D.value z.2 <;> simp [kernel, h]
  rw [heq]
  exact Measurable.ite (p := fun z => z.1 < D.value z.2)
    (measurableSet_lt (f := fun z : ℝ × Ω => z.1)
      (g := fun z : ℝ × Ω => D.value z.2) measurable_fst
      (D.measurable_value.comp measurable_snd))
    ((hG true).comp measurable_snd) ((hG false).comp measurable_snd)

/-- Integrating the fresh comparison uniform preserves the source's conditional coin credit. -/
theorem expectation (D : Model Ω S) (s : S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    (∫⁻ z, kernel D G z ∂ProductModel.posterior LatentUniform.model D ([], s)) =
      LatentCoin.credit D s (fun x => LatentBernoulli.bias (D.value x)) G := by
  change (∫⁻ z, kernel D G z ∂(DyadicPosterior.law []).prod (D.posterior s)) = _
  rw [DyadicPosterior.law_nil, lintegral_prod_symm _ (measurable_kernel D G hG).aemeasurable]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x => expectation_threshold (D.value x) (fun b => G b x)

/-- The unused fresh uniform can be discarded after the comparison, retaining full source credit. -/
theorem marginal_credit (D : Model Ω S) (p : List Bool) (s : S) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ z, F z.2 ∂ProductModel.posterior LatentUniform.model D (p, s)) =
      ∫⁻ x, F x ∂D.posterior s := by
  rw [ProductModel.expectation_right LatentUniform.model D (p, s)
    (fun z => F z.2) (hF.comp measurable_snd)]
  simp [ProductModel.rightCredit]

/-- The fresh nonatomic uniform is distinct from any measurable source value almost surely. -/
theorem ae_distinct (D : Model Ω S) (s : S) :
    ∀ᵐ z ∂ProductModel.posterior LatentUniform.model D ([], s),
      (ProductModel.left LatentUniform.model D).value z ≠
        (ProductModel.right LatentUniform.model D).value z := by
  change ∀ᵐ z ∂(DyadicPosterior.law []).prod (D.posterior s), z.1 ≠ D.value z.2
  have hm : MeasurableSet {z : ℝ × Ω | z.1 ≠ D.value z.2} :=
    (measurableSet_eq_fun measurable_fst (D.measurable_value.comp measurable_snd)).compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply (Measure.ae_ae_comm hm).mpr
  exact Filter.Eventually.of_forall fun x => (DyadicPosterior.law []).ae_ne (D.value x)

end

end SampLib.LatentReal.UniformThreshold
