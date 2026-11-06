module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! # The finite binomial product for shifted negative exponentials

The ith factor is exp(-choose(k,i) m^(k-i) p^i). Summing its exponents is exactly
the binomial theorem, including k=0 and m=0 with their usual zero-power convention.
-/

open Finset

namespace SampLib.BinomialShiftPower

noncomputable section

def coefficient (m k i : ℕ) : ℕ := k.choose i * m ^ (k - i)

def term (p : unitInterval) (m k i : ℕ) : ℝ := (coefficient m k i : ℝ) * (p : ℝ) ^ i

theorem term_nonneg (p : unitInterval) (m k i : ℕ) : 0 ≤ term p m k i :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.2.1 _)

/-- The unprocessed exponent beginning at the current loop index. -/
def value (p : unitInterval) (m k i : ℕ) : ℝ := ∑ j ∈ Ico i (k + 1), term p m k j

theorem value_nonneg (p : unitInterval) (m k i : ℕ) : 0 ≤ value p m k i :=
  sum_nonneg fun _ _ => term_nonneg p m k _

theorem value_step (p : unitInterval) (m k i : ℕ) (hi : i ≤ k) :
    value p m k i = term p m k i + value p m k (i + 1) :=
  sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hi) _

/-- The standard binomial theorem identifies the complete exponent. -/
theorem value_zero (p : unitInterval) (m k : ℕ) : value p m k 0 = ((m : ℝ) + p) ^ k := by
  rw [value, Nat.Ico_zero_eq_range, add_comm (m : ℝ), add_pow]
  apply sum_congr rfl
  intro i _
  simp only [term, coefficient, Nat.cast_mul, Nat.cast_pow]
  ring

def factorBias (p : unitInterval) (m k i : ℕ) : unitInterval :=
  ⟨Real.exp (-term p m k i), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (term_nonneg p m k i))⟩

def tailBias (p : unitInterval) (m k i : ℕ) : unitInterval :=
  ⟨Real.exp (-value p m k i), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (value_nonneg p m k i))⟩

/-- The requested shifted-power law, stated independently of the program recurrence. -/
def bias (p : unitInterval) (m k : ℕ) : unitInterval :=
  ⟨Real.exp (-(((m : ℝ) + p) ^ k)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (pow_nonneg (add_nonneg (Nat.cast_nonneg _) p.2.1) _))⟩

theorem tail_zero (p : unitInterval) (m k : ℕ) : tailBias p m k 0 = bias p m k := by
  apply Subtype.ext
  change Real.exp (-value p m k 0) = Real.exp (-(((m : ℝ) + p) ^ k))
  rw [value_zero]

theorem tail_step (p : unitInterval) (m k i : ℕ) (hi : i ≤ k) :
    tailBias p m k i = factorBias p m k i * tailBias p m k (i + 1) := by
  apply Subtype.ext
  change Real.exp (-value p m k i) =
    Real.exp (-term p m k i) * Real.exp (-value p m k (i + 1))
  rw [value_step p m k i hi, neg_add, Real.exp_add]

theorem tail_done (p : unitInterval) (m k i : ℕ) (hi : k < i) : tailBias p m k i = 1 := by
  apply Subtype.ext
  simp [tailBias, value, Ico_eq_empty_of_le (by omega : k + 1 ≤ i)]

/-- Repeating the exp(-p^i) coin implements precisely the ith binomial factor. -/
theorem factor_power (p : unitInterval) (m k i : ℕ) :
    Real.exp (-((p : ℝ) ^ i)) ^ coefficient m k i = (factorBias p m k i : ℝ) := by
  rw [← Real.exp_nat_mul]
  change Real.exp _ = Real.exp (-term p m k i)
  congr 1
  unfold term
  ring

/-- The complete finite product is exp(-(m+p)^k). -/
theorem product (p : unitInterval) (m k : ℕ) :
    (∏ i ∈ range (k + 1), Real.exp (-term p m k i)) = Real.exp (-(((m : ℝ) + p) ^ k)) := by
  rw [← Real.exp_sum, sum_neg_distrib]
  have h := value_zero p m k
  simp only [value, Nat.Ico_zero_eq_range] at h
  rw [h]

end

end SampLib.BinomialShiftPower
