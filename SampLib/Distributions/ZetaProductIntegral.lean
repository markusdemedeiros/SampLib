module

public import SampLib.Distributions.LatentReal.UniformVector
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic

@[expose] public section

/-! # The reciprocal of one plus a product of independent uniforms

The product's moments are `(m+1)⁻ᵏ`. For `k ≥ 2`, their sum is finite, so the
alternating geometric series can be integrated term by term, yielding Dirichlet's eta value.
-/

open MeasureTheory Set Finset

namespace SampLib.ZetaProductIntegral

noncomputable section

/-- The unsampled joint uniform law. -/
abbrev law (k : ℕ) := UniformVector.law (fun _ : Fin k => [])

def product {k : ℕ} (u : Fin k → ℝ) : ℝ := ∏ i, u i

theorem ae_coordinates (k : ℕ) : ∀ᵐ u ∂law k, ∀ i, u i ∈ Ico (0 : ℝ) 1 := by
  apply UniformVector.ae_coordinates
  intro i
  simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []

theorem product_mem {k : ℕ} {u : Fin k → ℝ} (hu : ∀ i, u i ∈ Ico (0 : ℝ) 1) :
    product u ∈ Icc (0 : ℝ) 1 :=
  ⟨prod_nonneg (fun i _ => (hu i).1),
    prod_le_one₀ (fun i _ => (hu i).1) (fun i _ => (hu i).2.le)⟩

theorem product_lt_one {k : ℕ} (hk : 0 < k) {u : Fin k → ℝ}
    (hu : ∀ i, u i ∈ Ico (0 : ℝ) 1) : product u < 1 := by
  let i : Fin k := ⟨0, hk⟩
  have hrest : ∏ j ∈ univ.erase i, u j ≤ 1 :=
    prod_le_one₀ (fun j _ => (hu j).1) (fun j _ => (hu j).2.le)
  calc
    product u = u i * ∏ j ∈ univ.erase i, u j :=
      (mul_prod_erase univ u (mem_univ i)).symm
    _ ≤ u i * 1 := mul_le_mul_of_nonneg_left hrest (hu i).1
    _ < 1 := by simpa only [mul_one] using (hu i).2

/-- Product moments factor into elementary one-dimensional power integrals. -/
theorem moment (k m : ℕ) :
    (∫ u, (product u) ^ m ∂law k) = 1 / ((m : ℝ) + 1) ^ k := by
  have hone : (∫ x, x ^ m ∂DyadicPosterior.unitLaw) = 1 / ((m : ℝ) + 1) := by
    change (∫ x in Ico (0 : ℝ) 1, x ^ m) = _
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    simp
  simp only [law, UniformVector.law, DyadicPosterior.law_nil, product, ← Finset.prod_pow]
  rw [integral_fintype_prod_eq_pow (fun x : ℝ => x ^ m), hone]
  simp

/-- The absolute geometric terms are integrable even though the pointwise bound has a pole. -/
theorem integrable_term (k m : ℕ) : Integrable (fun u => (-product u) ^ m) (law k) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold product; fun_prop)
  filter_upwards [ae_coordinates k] with u hu
  rw [norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg (product_mem hu).1]
  exact pow_le_one₀ (product_mem hu).1 (product_mem hu).2

theorem norm_moment (k m : ℕ) :
    (∫ u, ‖(-product u) ^ m‖ ∂law k) = 1 / ((m : ℝ) + 1) ^ k := by
  rw [← moment k m]
  apply integral_congr_ae
  filter_upwards [ae_coordinates k] with u hu
  simp only [norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg (product_mem hu).1]

theorem summable_moments {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ k) := by
  have h := (Real.summable_nat_pow_inv (p := k)).mpr (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using (summable_nat_add_iff 1).mpr h

/-- Absolute convergence permits integrating the geometric expansion without a boundary limit. -/
theorem integral_eq_alternating {k : ℕ} (hk : 2 ≤ k) :
    (∫ u, 1 / (1 + product u) ∂law k) =
      ∑' m : ℕ, (-1 : ℝ) ^ m / ((m : ℝ) + 1) ^ k := by
  have hm := hasSum_integral_of_summable_integral_norm (integrable_term k)
    (by simpa only [norm_moment] using summable_moments hk)
  have hgeom : (fun u => ∑' m : ℕ, (-product u) ^ m) =ᵐ[law k]
      (fun u => 1 / (1 + product u)) := by
    filter_upwards [ae_coordinates k] with u hu
    have h := hasSum_geometric_of_abs_lt_one (show |-product u| < 1 by
      rw [abs_neg, abs_of_nonneg (product_mem hu).1]
      exact product_lt_one (by omega) hu)
    simpa only [sub_neg_eq_add, one_div] using h.tsum_eq
  rw [integral_congr_ae hgeom] at hm
  convert hm.tsum_eq.symm using 1
  congr 1
  funext m
  have hterm : (fun u : Fin k → ℝ => (-product u) ^ m) =
      (fun u => (-1 : ℝ) ^ m * (product u) ^ m) := by
    funext u
    rw [neg_pow]
  rw [hterm, integral_const_mul, moment]
  simp only [div_eq_mul_inv, one_mul]

/-- Pairing the even and odd terms identifies eta with its absolutely convergent zeta series. -/
theorem alternating_eq_zeta {k : ℕ} (hk : 2 ≤ k) :
    (∑' m : ℕ, (-1 : ℝ) ^ m / ((m : ℝ) + 1) ^ k) =
      (1 - 2 / (2 : ℝ) ^ k) * (riemannZeta k).re := by
  let b : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) ^ k
  have hs : Summable b := summable_moments hk
  have he := hs.comp_injective (show Function.Injective (fun n : ℕ => 2 * n) by
    intro a b h
    dsimp at h
    omega)
  have ho := hs.comp_injective (show Function.Injective (fun n : ℕ => 2 * n + 1) by
    intro a b h
    dsimp at h
    omega)
  have hsplit : (∑' m, b (2 * m)) + (∑' m, b (2 * m + 1)) = ∑' m, b m :=
    tsum_even_add_odd he ho
  have hae : HasSum (fun m : ℕ => (-1 : ℝ) ^ (2 * m) / (((2 * m : ℕ) : ℝ) + 1) ^ k)
      (∑' m, b (2 * m)) := by
    simpa [Function.comp_def, b, pow_mul] using he.hasSum
  have hao : HasSum (fun m : ℕ => (-1 : ℝ) ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) + 1) ^ k)
      (-(∑' m, b (2 * m + 1))) := by
    simpa [Function.comp_def, b, pow_add, pow_mul, div_eq_mul_inv] using ho.hasSum.neg
  have ha := hae.even_add_odd
    (f := fun m : ℕ => (-1 : ℝ) ^ m / ((m : ℝ) + 1) ^ k) hao
  have hodd : (∑' m, b (2 * m + 1)) = (1 / (2 : ℝ) ^ k) * ∑' m, b m := by
    rw [← tsum_mul_left]
    congr 1
    funext m
    dsimp [b]
    push_cast
    rw [show (2 : ℝ) * m + 1 + 1 = 2 * (m + 1) by ring, mul_pow]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hz : (∑' m, b m) = (riemannZeta k).re := by
    have hc := zeta_eq_tsum_one_div_nat_add_one_cpow
      (s := (k : ℂ)) (show 1 < (k : ℂ).re by simp; omega)
    have hr : (↑(∑' m, b m) : ℂ) = riemannZeta k := by
      rw [Complex.ofReal_tsum, hc]
      congr 1
      funext m
      simp [b, Complex.cpow_natCast]
    simpa only [Complex.ofReal_re] using congrArg Complex.re hr
  rw [ha.tsum_eq]
  rw [hodd] at hsplit ⊢
  rw [← hz]
  linear_combination hsplit

/-- The zeta-related constant for every integer dimension at least two. -/
theorem integral_eq_zeta {k : ℕ} (hk : 2 ≤ k) :
    (∫ u, 1 / (1 + product u) ∂law k) =
      (1 - 2 / (2 : ℝ) ^ k) * (riemannZeta k).re :=
  (integral_eq_alternating hk).trans (alternating_eq_zeta hk)

/-- The usual eta factor, written with real powers rather than a quotient of natural powers. -/
theorem eta_factor (k : ℕ) :
    1 - 2 / (2 : ℝ) ^ k = 1 - (2 : ℝ) ^ (1 - (k : ℝ)) := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]

end

end SampLib.ZetaProductIntegral
