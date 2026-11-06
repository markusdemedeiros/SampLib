import SampLib.Distributions.MinimumComplementKernel
import SampLib.Distributions.MinimumComplementBarrier

/-! # A single continuation budget for the fair first-passage walk

The output expectation and escape probability are harmonic. Only the bounded
quadratic termination credit needs amplification; its expected decrease pays
for that amplification on every interior step.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.MinimumComplement

noncomputable section

open Barrier

private theorem fair_average (H : Bool → ℝ≥0∞) :
    (∫⁻ a, H a ∂RealCoin.law VonNeumann.fairBias) = (H true + H false) / 2 := by
  rw [RealCoin.lintegral_law]
  norm_num [RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.div_eq_inv_mul,
    mul_add]

/-- The two possible next states of the pending-level walk. -/
def next (k : ℕ) (a : Bool) : ℕ := if a then k + 1 else k - 1

private theorem auxiliary_budget (B k : ℕ) (hk : 0 < k) (hkB : k < B) (ε : ℝ≥0∞) :
    (∫⁻ a, (escape B (next k a) : ℝ≥0∞) +
      (amplifier B : ℝ≥0∞) * ε * (potential B (next k a) : ℝ≥0∞)
      ∂RealCoin.law VonNeumann.fairBias) ≤
        (escape B k : ℝ≥0∞) + ε * (potential B k : ℝ≥0∞) := by
  rw [fair_average]
  simp only [next, ite_true, Bool.false_eq_true, ite_false]
  calc
    _ = ((escape B (k - 1) + escape B (k + 1)) / 2 : ℝ≥0) +
        ε * (amplifier B / 2 * (potential B (k - 1) + potential B (k + 1)) : ℝ≥0) := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, div_eq_mul_inv]
      norm_num
      ring
    _ ≤ _ := by
      rw [escape_harmonic B k hk]
      apply add_le_add le_rfl
      gcongr
      exact amplification_bound B k hk hkB

/-- Output, escape, and amplified termination credits fit the current budget. -/
theorem expectation (t : unitInterval) (B k s : ℕ) (hk : 0 < k) (hkB : k < B)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ a,
      RealCoin.credit (Walk.bias t (next k a) (s + 1)) F +
        ((escape B (next k a) : ℝ≥0∞) +
          (amplifier B : ℝ≥0∞) * ε * (potential B (next k a) : ℝ≥0∞))
      ∂RealCoin.law VonNeumann.fairBias) ≤
        RealCoin.credit (Walk.bias t k s) F +
          ((escape B k : ℝ≥0∞) + ε * (potential B k : ℝ≥0∞)) := by
  have hstep : (∫⁻ a, RealCoin.credit (Walk.bias t (next k a) (s + 1)) F
      ∂RealCoin.law VonNeumann.fairBias) = RealCoin.credit (Walk.bias t k s) F := by
    have h := Walk.expectation t (k - 1) s F
    rw [fair_average] at h ⊢
    simpa only [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega,
      CoinConditional.firstCredit, RealCoin.lintegral_law, next, ite_true,
      Bool.false_eq_true, ite_false, add_comm] using h
  rw [lintegral_add_left (measurable_of_countable _), hstep]
  exact add_le_add le_rfl (auxiliary_budget B k hk hkB ε)

/-- Move the upper barrier out and shrink the local termination slack together. -/
theorem initial_slack (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ (B : ℕ) (η : ℝ≥0), 2 ≤ B ∧ 0 < η ∧
      escape B 1 + η * potential B 1 ≤ δ := by
  obtain ⟨B, hB, hescape⟩ := exists_barrier ((δ : ℝ) / 2) (by positivity)
  have hBpos : 0 < B := by omega
  let η : ℝ≥0 := δ / (2 * B)
  have hη : 0 < η := div_pos hδ (by positivity)
  have hproduct : η * potential B 1 = δ / 2 := by
    rw [potential_one B hBpos]
    dsimp [η]
    have hBne : (B : ℝ≥0) ≠ 0 := by exact_mod_cast hBpos.ne'
    field_simp
  refine ⟨B, η, hB, hη, ?_⟩
  rw [hproduct, ← NNReal.coe_le_coe]
  simpa only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat] using
    (show (escape B 1 : ℝ) + (δ : ℝ) / 2 ≤ δ by linarith)

end

end SampLib.MinimumComplement
