import SampLib.Distributions.DyadicRefinement
import SampLib.Samplers.CoinMean

/-! # Bernoulli kernels over a cached uniform

A measurable continuation may depend on both the returned bit and the same latent
uniform. Such credits retain the correlation between repeated calls on one bag.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.LatentBernoulli

noncomputable section

/-- A measurable global extension of the latent uniform's unit-interval bias. -/
def bias (u : ℝ) : unitInterval := projIcc 0 1 zero_le_one u

theorem measurable_bias : Measurable bias := by
  unfold bias projIcc
  fun_prop

theorem bias_coe {u : ℝ} (hu : u ∈ Ico 0 1) : (bias u : ℝ) = u := by
  simp only [bias, projIcc_of_mem zero_le_one ⟨hu.1, hu.2.le⟩]

/-- Conditional expectation of an output/latent continuation. -/
def kernel (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  RealCoin.credit (φ u) (fun b => G b u)

theorem measurable_kernel {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) : Measurable (kernel φ G) := by
  have ht := hG true
  have hf := hG false
  unfold kernel RealCoin.credit RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  fun_prop

/-- Posterior expected credit for a conditional Bernoulli draw. -/
def credit (p : List Bool) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  DyadicPosterior.credit p (kernel φ G)

/-- A fixed independent coin commutes with posterior integration. -/
theorem credit_fixed_bias (p : List Bool) (q : unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    credit p (fun _ => q) G =
      RealCoin.credit q (fun b => DyadicPosterior.credit p (G b)) := by
  unfold credit kernel DyadicPosterior.credit RealCoin.credit RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  have ht : Measurable (fun u => ENNReal.ofReal (q : ℝ) * G true u) :=
    measurable_const.mul (hG true)
  calc
    _ = (∫⁻ u, ENNReal.ofReal (q : ℝ) * G true u ∂DyadicPosterior.law p) +
        ∫⁻ u, ENNReal.ofReal (1 - (q : ℝ)) * G false u ∂DyadicPosterior.law p :=
      lintegral_add_left ht _
    _ = _ := by rw [lintegral_const_mul _ (hG true), lintegral_const_mul _ (hG false)]

/-- A normalized posterior leaves constant auxiliary credit unchanged. -/
theorem posterior_add_const (p : List Bool) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (c : ℝ≥0∞) :
    DyadicPosterior.credit p (fun u => F u + c) = DyadicPosterior.credit p F + c := by
  unfold DyadicPosterior.credit
  calc
    _ = (∫⁻ u, F u ∂DyadicPosterior.law p) + ∫⁻ _, c ∂DyadicPosterior.law p :=
      lintegral_add_left hF _
    _ = _ := by simp

/-- Pointwise, a geometric digit chooses the head or a Bernoulli tail with equal weights. -/
theorem half_kernel (head : Bool) (G : Bool → ℝ → ℝ≥0∞) (u : ℝ)
    (hu : u ∈ Ico 0 1) :
    kernel bias G (DyadicPosterior.half head u) =
      (G head (DyadicPosterior.half head u) +
        kernel bias (fun b v => G b (DyadicPosterior.half head v)) u) / 2 := by
  let h : unitInterval := if head then 1 else 0
  have hh : DyadicPosterior.half head u ∈ Ico 0 1 := by
    simpa only [DyadicPosterior.embed] using DyadicPosterior.embed_mem_unit [head] hu
  have hm : CoinMean.bias h (bias u) = bias (DyadicPosterior.half head u) := by
    apply Subtype.ext
    change (1 - (1 / 2 : ℝ)) * (bias u : ℝ) + (1 / 2 : ℝ) * (h : ℝ) = _
    rw [bias_coe hu, bias_coe hh]
    cases head <;> norm_num [h, DyadicPosterior.half] <;> ring
  have hc := CoinMean.expectation_preservation h (bias u)
    (fun b => G b (DyadicPosterior.half head u))
  rw [← FairCoin.expectation, CoinMean.law, hm, RealCoin.lintegral_law] at hc
  cases head <;>
    simpa [kernel, h, CoinConditional.firstCredit, Finset.sum_range_succ,
      RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, add_comm] using hc.symm

/-- Credit for the fair choice between the cached head and a recursive tail draw. -/
def selectorCredit (p : List Bool) (head : Bool) (G : Bool → ℝ → ℝ≥0∞)
    (ε : ℝ≥0∞) (select : Bool) : ℝ≥0∞ :=
  if select then DyadicPosterior.credit (head :: p) (G head)
  else credit p bias (fun b u => G b (DyadicPosterior.half head u)) + 2 * ε

/-- The affine Bernoulli identity preserves posterior credit and pays one retry ε on average. -/
theorem expectation (p : List Bool) (head : Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) :
    (∫⁻ select, selectorCredit p head G ε select ∂RealCoin.law VonNeumann.fairBias) =
      credit (head :: p) bias G + ε := by
  have hhead : Measurable (fun u => G head (DyadicPosterior.half head u)) :=
    (hG head).comp (DyadicPosterior.measurable_half head)
  have htail : Measurable
      (fun u => kernel bias (fun b v => G b (DyadicPosterior.half head v)) u) :=
    measurable_kernel measurable_bias
      (fun b => (hG b).comp (DyadicPosterior.measurable_half head))
  have hsplit : credit (head :: p) bias G =
      (DyadicPosterior.credit (head :: p) (G head) +
        credit p bias (fun b u => G b (DyadicPosterior.half head u))) / 2 := by
    rw [credit, DyadicPosterior.credit_cons head p _ (measurable_kernel measurable_bias hG),
      DyadicPosterior.credit_cons head p _ (hG head)]
    unfold DyadicPosterior.credit
    rw [lintegral_congr_ae ((DyadicPosterior.ae_mem_unit p).mono
      (fun u hu => half_kernel head G u hu))]
    simp only [ENNReal.div_eq_inv_mul]
    have hsum : Measurable (fun u => G head (DyadicPosterior.half head u) +
        kernel bias (fun b v => G b (DyadicPosterior.half head v)) u) := hhead.add htail
    rw [lintegral_const_mul _ hsum]
    congr 1
    exact lintegral_add_left hhead _
  rw [hsplit, RealCoin.lintegral_law]
  norm_num [selectorCredit, RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc
    _ = (DyadicPosterior.credit (head :: p) (G head) +
        credit p bias (fun b u => G b (DyadicPosterior.half head u))) / 2 +
        ((2 : ℝ≥0∞)⁻¹ * 2) * ε := by
      simp only [ENNReal.div_eq_inv_mul]
      ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

end

end SampLib.LatentBernoulli
