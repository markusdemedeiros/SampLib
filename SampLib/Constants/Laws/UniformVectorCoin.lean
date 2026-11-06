import SampLib.Latent.UniformVectorModel
import SampLib.Latent.LatentCoinSpec
import SampLib.Latent.Laws.LatentBernoulli
import SampLib.Bernoulli.CoinProduct

/-! # One conditional coin in a joint uniform world

Fubini integrates every other coordinate into the continuation of the selected
bag. Both output credits retain their full dependence on the latent vector.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

/-- A geometric-bag call uses precisely the selected latent coordinate. -/
def coinBias {n : ℕ} (i : Fin n) (z : Fin n → ℝ) : unitInterval :=
  LatentBernoulli.bias (z i)

theorem measurable_coinBias {n : ℕ} (i : Fin n) : Measurable (coinBias i) :=
  LatentBernoulli.measurable_bias.comp (measurable_pi_apply i)

private theorem coordinate_kernel {n : ℕ} (p : Fin (n + 1) → List Bool)
    (i : Fin (n + 1)) (G : Bool → (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (x : ℝ) :
    coordinateCredit p i (LatentReal.LatentCoin.kernel (coinBias i) G) x =
      LatentBernoulli.kernel LatentBernoulli.bias (fun b => coordinateCredit p i (G b)) x := by
  have heval (others : Fin n → ℝ) : join i (x, others) i = x := by
    simp [join, MeasurableEquiv.piFinSuccAbove_symm_apply]
  unfold coordinateCredit LatentReal.LatentCoin.kernel LatentBernoulli.kernel
    RealCoin.credit RealCoin.pmf coinBias
  simp only [heval, ite_true, Bool.false_eq_true, ite_false]
  have hm (b : Bool) : Measurable (fun others => G b (join i (x, others))) :=
    (hG b).comp ((join i).measurable.comp (measurable_const.prodMk measurable_id))
  have ht : Measurable (fun others : Fin n → ℝ =>
      ENNReal.ofReal (LatentBernoulli.bias x : ℝ) * G true (join i (x, others))) :=
    measurable_const.mul (hm true)
  rw [lintegral_add_left ht,
    lintegral_const_mul _ (hm true), lintegral_const_mul _ (hm false)]

/-- One-coordinate Bernoulli credit is the full joint credit, before revealing any bits. -/
theorem coin_expectation {n : ℕ} (p : Fin (n + 1) → List Bool) (i : Fin (n + 1))
    (G : Bool → (Fin (n + 1) → ℝ) → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    LatentReal.LatentCoin.credit (world (n + 1)) p (coinBias i) G =
      LatentBernoulli.credit (p i) LatentBernoulli.bias
        (fun b => coordinateCredit p i (G b)) := by
  change (∫⁻ z, LatentReal.LatentCoin.kernel (coinBias i) G z ∂law p) = _
  rw [expectation_coordinate p i _
    (LatentReal.LatentCoin.measurable_kernel (measurable_coinBias i) hG)]
  simp_rw [coordinate_kernel p i G hG]
  rfl

/-- Conditional conjunction of the selected coordinate coins. -/
def productBias {n : ℕ} (indices : List (Fin n)) (z : Fin n → ℝ) : unitInterval :=
  (indices.map (fun i => coinBias i z)).prod

theorem measurable_productBias {n : ℕ} (indices : List (Fin n)) :
    Measurable (productBias indices) := by
  induction indices with
  | nil => exact measurable_const
  | cons i indices ih => exact (measurable_coinBias i).mul ih

/-- An empty conjunction returns true without changing the joint posterior. -/
theorem product_nil_credit {n : ℕ} (p : Fin n → List Bool)
    (G : Bool → (Fin n → ℝ) → ℝ≥0∞) :
    LatentReal.LatentCoin.credit (world n) p (productBias []) G =
      ∫⁻ z, G true z ∂law p := by
  simp [LatentReal.LatentCoin.credit, LatentReal.LatentCoin.kernel, productBias,
    RealCoin.credit, RealCoin.pmf, world]

/-- On success the next selected coordinate is tested; failure returns immediately. -/
def productInputCredit {n : ℕ} (indices : List (Fin n))
    (G : Bool → (Fin n → ℝ) → ℝ≥0∞) (b : Bool) (z : Fin n → ℝ) : ℝ≥0∞ :=
  if b then LatentReal.LatentCoin.kernel (productBias indices) G z else G false z

theorem measurable_productInputCredit {n : ℕ} (indices : List (Fin n))
    (G : Bool → (Fin n → ℝ) → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (b : Bool) :
    Measurable (productInputCredit indices G b) := by
  cases b
  · exact hG false
  · exact LatentReal.LatentCoin.measurable_kernel (measurable_productBias indices) hG

/-- The conjunction identity is applied before averaging over the shared latent world. -/
theorem product_expectation {n : ℕ} (p : Fin n → List Bool) (i : Fin n)
    (indices : List (Fin n)) (G : Bool → (Fin n → ℝ) → ℝ≥0∞) :
    LatentReal.LatentCoin.credit (world n) p (coinBias i) (productInputCredit indices G) =
      LatentReal.LatentCoin.credit (world n) p (productBias (i :: indices)) G := by
  apply lintegral_congr
  intro z
  simpa only [productInputCredit, LatentReal.LatentCoin.kernel, productBias,
    List.map_cons, List.prod_cons, CoinProduct.firstCredit, RealCoin.lintegral_law,
    CoinProduct.law] using
    CoinProduct.expectation_preservation (coinBias i z) (productBias indices z) (fun b => G b z)

end

end SampLib.UniformVector
