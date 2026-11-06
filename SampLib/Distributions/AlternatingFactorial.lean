module

public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Mathlib.Data.Nat.Factorial.BigOperators

@[expose] public section

/-! # Alternating factorial trials

The successive continuation probabilities are `t/i`. Their finite products give
factorial tails; parity at the first failure recovers the exponential series.
-/

open Finset
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.AlternatingFactorial

noncomputable section

/-- Probability of continuing at the current denominator. -/
def hazard (t : unitInterval) (i : ℕ) : ℝ≥0∞ := ofReal ((t : ℝ) / i)

/-- Probability of exactly `n` continuations before stopping. -/
def mass (t : unitInterval) (i n : ℕ) : ℝ≥0∞ :=
  (∏ j ∈ range n, hazard t (i + j)) * ofReal (1 - (t : ℝ) / (i + n))

@[simp] theorem mass_zero (t : unitInterval) (i : ℕ) :
    mass t i 0 = ofReal (1 - (t : ℝ) / i) := by simp [mass]

theorem mass_succ (t : unitInterval) (i n : ℕ) :
    mass t i (n + 1) = hazard t i * mass t (i + 1) n := by
  simp only [mass, prod_range_succ', Nat.add_zero]
  have hp : (∏ j ∈ range n, hazard t (i + (j + 1))) =
      ∏ j ∈ range n, hazard t (i + 1 + j) := by
    apply prod_congr rfl
    intro j _
    congr 1
    omega
  rw [hp]
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : ℝ)]
  ring

/-- Expected continuation credit after the parity of the first failure is read. -/
def credit (t : unitInterval) (i : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  ∑' n, mass t i n * F (if n % 2 = 0 then b else !b)

private theorem parity_succ (n : ℕ) (b : Bool) :
    (if (n + 1) % 2 = 0 then b else !b) =
      (if n % 2 = 0 then !b else !!b) := by
  obtain h | h := Nat.mod_two_eq_zero_or_one n <;> simp [Nat.add_mod, h]

/-- Separate the first failure from one continuation and a parity reversal. -/
theorem credit_step (t : unitInterval) (i : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) :
    credit t i F b = ofReal (1 - (t : ℝ) / i) * F b +
      hazard t i * credit t (i + 1) F (!b) := by
  rw [credit, tsum_eq_zero_add' ENNReal.summable]
  simp only [mass_zero, Nat.zero_mod, ite_true, mass_succ, parity_succ, mul_assoc]
  rw [credit, ENNReal.tsum_mul_left]

private theorem survival_one (t : unitInterval) (n : ℕ) :
    (∏ j ∈ range n, hazard t (1 + j)) = ofReal ((t : ℝ) ^ n / n.factorial) := by
  unfold hazard
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    div_nonneg t.2.1 (Nat.cast_nonneg _))]
  congr 1
  rw [prod_div_distrib]
  simp only [prod_const, card_range]
  have hd : (∏ j ∈ range n, ((1 + j : ℕ) : ℝ)) = n.factorial := by
    exact_mod_cast (show (∏ j ∈ range n, (1 + j)) = n.factorial by
      simpa only [Nat.add_comm] using prod_range_add_one_eq_factorial n)
  rw [hd]

theorem mass_one (t : unitInterval) (n : ℕ) :
    mass t 1 n = ProbLang.TotalEris.Examples.RealDecrTrialPMF₀ t n := by
  rw [mass, survival_one,
    ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg t.2.1 _) (Nat.cast_nonneg _))]
  unfold ProbLang.TotalEris.Examples.RealDecrTrialPMF₀
  congr 1
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- At denominator one, the even/odd factorial sums are `exp(-t)` and its complement. -/
theorem credit_one (t : unitInterval) (F : Bool → ℝ≥0∞) :
    credit t 1 F true = ofReal (Real.exp (-(t : ℝ))) * F true +
      ofReal (1 - Real.exp (-(t : ℝ))) * F false := by
  simp only [credit, mass_one, Bool.not_true, apply_ite F]
  simpa only [ProbLang.TotalEris.Examples.RealDecrTrialCreditV,
    ProbLang.TotalEris.Examples.RealDecrTrialPMF_base] using
    ProbLang.TotalEris.Examples.RealDecrTrialCreditV_parity (F true) (F false) t.2.1 t.2.2

end

end SampLib.AlternatingFactorial
