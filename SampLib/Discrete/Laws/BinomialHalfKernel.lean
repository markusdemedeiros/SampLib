import SampLib.Discrete.Laws.BinomialHalfMoment

/-! # Credit conservation for half-binomial rejection -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.BinomialHalfProposal

noncomputable section

open BinomialHalfEnvelope

/-- Exact reciprocal retry probability. -/
def factor : ℝ≥0 := 16 / 15

theorem one_lt_factor : 1 < factor := by norm_num [factor]

/-- Credit after a proposal: accept the candidate or repeat with amplified slack. -/
def kernel (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : ℕ × (Fin (width n) × Bool)) : ℝ≥0∞ :=
  ENNReal.ofReal (acceptance n t) * F (candidate n t).toNat +
    ENNReal.ofReal (1 - acceptance n t) *
      ((∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n) + factor * ε)

/-- One sixteenth of each binomial moment exits; fifteen sixteenths repeats. -/
theorem expectation (n : ℕ) (hn : Even n) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ t, kernel n F ε t ∂law n =
      (∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n) + ε := by
  have hm : (∫⁻ t, ENNReal.ofReal (acceptance n t) ∂law n) = 1 / 16 := by
    simpa using accepted_expectation n hn (fun _ => 1)
  have hparts : (∫⁻ t, ENNReal.ofReal (1 - acceptance n t) ∂law n) + 1 / 16 = 1 := by
    rw [← hm, ← lintegral_add_left (measurable_of_countable _) _]
    have hpoint (t : ℕ × (Fin (width n) × Bool)) :
        ENNReal.ofReal (1 - acceptance n t) + ENNReal.ofReal (acceptance n t) = 1 := by
      have ht := acceptance_mem n hn t
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
      norm_num
    simp_rw [hpoint]
    simp
  have hr : (∫⁻ t, ENNReal.ofReal (1 - acceptance n t) ∂law n) = 15 / 16 := by
    apply (ENNReal.add_left_inj (by norm_num : (1 / 16 : ℝ≥0∞) ≠ ∞)).mp
    rw [hparts]
    rw [ENNReal.div_add_div_same]
    norm_num [ENNReal.div_self]
  unfold kernel
  rw [lintegral_add_left (measurable_of_countable _) _, accepted_expectation n hn,
    lintegral_mul_const _ (measurable_of_countable _), hr]
  have hsum : (1 / 16 : ℝ≥0∞) + 15 / 16 = 1 := by
    rw [ENNReal.div_add_div_same]
    norm_num [ENNReal.div_self]
  have hamp : (15 / 16 : ℝ≥0∞) * (factor : ℝ≥0∞) = 1 := by
    rw [factor, ENNReal.coe_div (by norm_num)]
    norm_num only [ENNReal.coe_ofNat]
    rw [ENNReal.div_mul_div_cancel (by norm_num) (by norm_num)]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  calc
    _ = ((1 / 16 : ℝ≥0∞) + 15 / 16) *
        (∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n) +
          ((15 / 16 : ℝ≥0∞) * factor) * ε := by ring
    _ = _ := by rw [hsum, hamp, one_mul, one_mul]

end

end SampLib.BinomialHalfProposal
