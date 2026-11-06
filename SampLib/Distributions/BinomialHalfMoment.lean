import SampLib.Distributions.BinomialHalfAcceptance
import SampLib.Distributions.Binomial

/-! # The accepted moment of half-binomial rejection

The block proposal cancels its acceptance weight, leaving exactly one sixteenth
of the half-binomial law. No integrability restriction is imposed on credits.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.BinomialHalfProposal

noncomputable section

open BinomialHalfEnvelope

/-- Half-binomial masses in the denominator form used by rejection. -/
theorem half_binomial_mass (n k : ℕ) :
    Binomial.law VonNeumann.fairBias n {k} =
      ENNReal.ofReal ((Nat.choose n k : ℝ) / 2 ^ n) := by
  rw [Binomial.law_singleton]
  by_cases hk : k ≤ n
  · simp only [RealCoin.pmf, VonNeumann.fairBias, ↓reduceIte, Bool.false_eq_true,
      sub_half]
    rw [← ENNReal.ofReal_natCast (n.choose k), ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk, one_div_pow]
    simp only [div_eq_mul_inv, one_mul]
  · simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

/-- Every accepted integer appears once; negative and out-of-range candidates vanish. -/
theorem accepted_expectation (n : ℕ) (hn : Even n) (F : ℕ → ℝ≥0∞) :
    ∫⁻ t, ENNReal.ofReal (acceptance n t) * F (candidate n t).toNat ∂law n =
      (1 / 16 : ℝ≥0∞) * ∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n := by
  rw [lintegral_countable']
  have hterm (t : ℕ × (Fin (width n) × Bool)) :
      ENNReal.ofReal (acceptance n t) * F (candidate n t).toNat * law n {t} =
        if 0 ≤ candidate n t ∧ candidate n t ≤ n then
          ENNReal.ofReal ((Nat.choose n (candidate n t).toNat : ℝ) / 2 ^ (n + 4)) *
            F (candidate n t).toNat else 0 := by
    rw [mul_right_comm, accepted_atom n hn]
    split_ifs <;> simp
  simp_rw [hterm]
  simp_rw [← candidateEquiv_apply]
  rw [(candidateEquiv n).tsum_eq (fun z : ℤ =>
    if 0 ≤ z ∧ z ≤ n then
      ENNReal.ofReal ((Nat.choose n z.toNat : ℝ) / 2 ^ (n + 4)) * F z.toNat else 0)]
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hneg : (∑' k : ℕ, if 0 ≤ (-(k + 1) : ℤ) ∧ (-(k + 1) : ℤ) ≤ n then
      ENNReal.ofReal ((Nat.choose n (-(k + 1) : ℤ).toNat : ℝ) / 2 ^ (n + 4)) *
        F (-(k + 1) : ℤ).toNat else 0) = 0 := by
    calc
      _ = ∑' _ : ℕ, (0 : ℝ≥0∞) := by
        apply tsum_congr
        intro k
        rw [ite_eq_right (by omega)]
      _ = 0 := by simp
  rw [hneg, add_zero, lintegral_countable', ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [half_binomial_mass]
  by_cases hk : k ≤ n
  · have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
    simp only [Int.natCast_nonneg, hk', and_self, ↓reduceIte, Int.toNat_natCast]
    have hreal : (Nat.choose n k : ℝ) / 2 ^ (n + 4) =
        (1 / 16 : ℝ) * ((Nat.choose n k : ℝ) / 2 ^ n) := by
      rw [pow_add]
      norm_num
      ring
    rw [hreal, ENNReal.ofReal_mul (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos]
    ring
  · simp [hk, Nat.choose_eq_zero_of_lt (by omega : n < k)]

end

end SampLib.BinomialHalfProposal
