module

public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Rational Bernoulli bias and its rank kernel

A uniform rank below `b` carries the credit of `decide (k < a)`. Counting ranks below the
threshold gives the Bernoulli expectation with bias `a / b`.
-/

open Finset
open ENNReal (ofReal ofReal_div_of_pos div_eq_inv_mul)
open scoped ENNReal

namespace SampLib.RationalCoin

noncomputable section

/-- The valid rational input, regarded as a probability. -/
def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) : unitInterval :=
  ⟨(a : ℝ) / (b : ℝ), div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le),
    (div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)⟩

/-- Credit assigned to a uniform integer rank. -/
def rankCredit (a : ℤ) (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if (k : ℤ) < a then F true else F false

/-- Counting ranks below the threshold gives the rational Bernoulli expectation. -/
theorem expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range b.toNat, rankCredit a F k) / b.toNat =
      RealCoin.credit (bias a b ha hb hab) F := by
  have hab' : a.toNat ≤ b.toNat := by omega
  have hlt (k : ℕ) : (k : ℤ) < a ↔ k < a.toNat := by omega
  have hsum : (∑ k ∈ range b.toNat, rankCredit a F k) =
      (a.toNat : ℝ≥0∞) * F true + ((b.toNat - a.toNat : ℕ) : ℝ≥0∞) * F false := by
    simp only [rankCredit, hlt]
    conv_lhs => rw [← Nat.add_sub_of_le hab', sum_range_add]
    congr 1
    · calc
        _ = ∑ k ∈ range a.toNat, F true :=
          sum_congr rfl fun k hk => ite_eq_left (mem_range.mp hk)
        _ = _ := by simp [nsmul_eq_mul]
    · simp [Nat.not_lt.mpr (Nat.le_add_right a.toNat _), nsmul_eq_mul]
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have haCast : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  have hbCast : (b.toNat : ℝ) = (b : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hb.le
  have ht : ofReal ((a : ℝ) / b) =
      (a.toNat : ℝ≥0∞) / b.toNat := by
    rw [← haCast, ← hbCast,
      ofReal_div_of_pos (by exact_mod_cast (show 0 < b.toNat by omega))]
    simp
  have hc : (1 : ℝ) - (a : ℝ) / b = ((b.toNat - a.toNat : ℕ) : ℝ) / b.toNat := by
    rw [Nat.cast_sub hab', haCast, hbCast]
    field_simp
  have hf : ofReal (1 - (a : ℝ) / b) =
      ((b.toNat - a.toNat : ℕ) : ℝ≥0∞) / b.toNat := by
    rw [hc, ofReal_div_of_pos (by exact_mod_cast (show 0 < b.toNat by omega))]
    simp
  rw [hsum]
  simp only [RealCoin.credit, RealCoin.pmf, bias, Bool.false_eq_true, ite_true, ite_false, ht, hf,
    div_eq_inv_mul]
  ring

theorem zero_credit (b : ℤ) (ha : (0 : ℤ) ≤ 0) (hb : 0 < b) (hab : 0 ≤ b)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (bias 0 b ha hb hab) F = F false := by
  simp [RealCoin.credit, RealCoin.pmf, bias]

theorem full_credit (b : ℤ) (ha : 0 ≤ b) (hb : 0 < b) (hab : b ≤ b)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (bias b b ha hb hab) F = F true := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [RealCoin.credit, RealCoin.pmf, bias, hbR]

theorem rankCredit_eq (a : ℤ) (F : Bool → ℝ≥0∞) (k : ℕ) :
    rankCredit a F k = F (decide ((k : ℤ) < a)) := by
  by_cases h : (k : ℤ) < a <;> simp [rankCredit, h]

end

end SampLib.RationalCoin
