import SampLib.Distributions.GroupedEnvelope
import SampLib.Samplers.RationalCoin

/-! # Uniform cells and acceptance coins inside a dyadic envelope -/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.GroupedEnvelope

noncomputable section

/-- Each uniformly proposed cell pays its labelled weight or the unused envelope. -/
def candidateCredit (_n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞)
    (R : ℝ≥0∞) (k r : ℕ) : ℝ≥0∞ :=
  ((weight (position k r) : ℝ≥0∞) * F (position k r) +
    ((envelope k - weight (position k r) : ℕ) : ℝ≥0∞) * R) / envelope k

/-- Averaging a group's cells gives its rectangular credit. -/
theorem candidate_expectation (n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞)
    (R : ℝ≥0∞) (k : ℕ) :
    (∫⁻ r, candidateCredit n weight envelope F R k r ∂UniformInt.law (DyadicGroups.width n k)) =
      groupCredit n weight envelope F R k := by
  rw [UniformInt.lintegral_law]
  simp only [candidateCredit]
  rw [← ENNReal.sum_div]
  unfold groupCredit numerator mass
  simp only [Nat.cast_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast (DyadicGroups.width_pos n k).ne' :
      (DyadicGroups.width n k : ℝ≥0∞) ≠ 0))
    (Or.inl (by finiteness : (DyadicGroups.width n k : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))]
  ring

/-- The rational acceptance coin realizes the true and unused integer widths. -/
theorem candidate_coin (n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞)
    (R : ℝ≥0∞) (k r : ℕ) (he : 0 < envelope k)
    (hw : weight (position k r) ≤ envelope k) :
    RealCoin.credit
      (RationalCoin.bias (weight (position k r)) (envelope k) (by positivity)
        (by exact_mod_cast he) (by exact_mod_cast hw))
      (fun b => if b then F (position k r) else R) = candidateCredit n weight envelope F R k r := by
  have heR : (0 : ℝ) < envelope k := by positivity
  have hc : 1 - (weight (position k r) : ℝ) / envelope k =
      ((envelope k - weight (position k r) : ℕ) : ℝ) / envelope k := by
    rw [Nat.cast_sub hw]
    field_simp
  simp only [RealCoin.credit, RealCoin.pmf, RationalCoin.bias,
    Bool.false_eq_true, ite_true, ite_false, Int.cast_natCast, candidateCredit]
  rw [hc, ENNReal.ofReal_div_of_pos heR, ENNReal.ofReal_div_of_pos heR]
  simp only [ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
  ring

end

end SampLib.GroupedEnvelope
