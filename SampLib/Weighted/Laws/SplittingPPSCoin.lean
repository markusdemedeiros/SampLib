import SampLib.Weighted.Laws.SplittingPPSLaw
import SampLib.Common.Laws.Urn

/-! # The supported split and its continuation credit -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SplittingPPS

noncomputable section

variable {size count : ℕ}

def splitBias (s : State size count) (hc : 0 < count) (hs : count < size) : unitInterval :=
  RationalCoin.bias s.amount s.denominator (by omega) (by exact_mod_cast s.positive)
    (by exact_mod_cast (s.amount_bounds hc hs).2.1)

theorem splitBias_eq_urn (s : State size count) (hc : 0 < count) (hs : count < size) :
    splitBias s hc hs = Urn.bias s.amount (s.denominator - s.amount) := by
  have heq := Nat.add_sub_of_le (s.amount_bounds hc hs).2.1
  have hp : 0 < s.amount + (s.denominator - s.amount) := by rw [heq]; exact s.positive
  apply Subtype.ext
  simp only [splitBias, Urn.bias, dite_eq_left hp, RationalCoin.bias]
  simp only [Nat.cast_sub (s.amount_bounds hc hs).2.1]
  push_cast
  ring

theorem split_pmf_true (s : State size count) (hc : 0 < count) (hs : count < size) :
    RealCoin.pmf (splitBias s hc hs) true = (s.amount : ℝ≥0∞) / s.denominator := by
  rw [splitBias_eq_urn, Urn.pmf_true]
  · rw [← Nat.cast_add, Nat.add_sub_of_le (s.amount_bounds hc hs).2.1]
  · have := s.positive
    omega

theorem split_pmf_false (s : State size count) (hc : 0 < count) (hs : count < size) :
    RealCoin.pmf (splitBias s hc hs) false =
      ((s.denominator - s.amount : ℕ) : ℝ≥0∞) / s.denominator := by
  rw [splitBias_eq_urn, Urn.pmf_false]
  · rw [← Nat.cast_add, Nat.add_sub_of_le (s.amount_bounds hc hs).2.1]
  · have := s.positive
    omega

/-- A terminal split accepts surely; every actual rejection has a positive residual denominator. -/
theorem split_support (s : State size count) (hc : 0 < count) (hs : count < size) :
    ∀ᵐ b ∂RealCoin.law (splitBias s hc hs), b = true ∨ s.amount < s.denominator := by
  by_cases hn : s.amount < s.denominator
  · exact Filter.Eventually.of_forall (fun _ => Or.inr hn)
  · have heq : s.amount = s.denominator := by
      have := (s.amount_bounds hc hs).2.1
      omega
    simp only [RealCoin.law, split_pmf_false, heq, Nat.sub_self, Nat.cast_zero, ENNReal.zero_div,
      zero_smul, add_zero]
    apply Measure.ae_smul_measure
    simp only [ae_dirac_eq, Filter.eventually_pure, true_or]

def branchCredit (s : State size count) (hc : 0 < count) (hs : count < size)
    (F : List ℤ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F s.topLabels else
    if hn : s.amount < s.denominator then ∫⁻ xs, F xs ∂law hc hs (s.next hc hs hn) else 0

/-- The split distributes precisely the joint-law continuation credit. -/
theorem split_expectation (s : State size count) (hc : 0 < count) (hs : count < size)
    (F : List ℤ → ℝ≥0∞) :
    ∫⁻ b, branchCredit s hc hs F b ∂RealCoin.law (splitBias s hc hs) =
      ∫⁻ xs, F xs ∂law hc hs s := by
  rw [RealCoin.lintegral_law, RealCoin.credit, split_pmf_true, split_pmf_false,
    expectation hc hs s]
  by_cases hn : s.amount < s.denominator
  · simp only [branchCredit, ite_true, Bool.false_eq_true, ite_false, dite_eq_left hn]
  · have heq : s.amount = s.denominator := by
      have := (s.amount_bounds hc hs).2.1
      omega
    simp only [branchCredit, ite_true, Bool.false_eq_true, ite_false, dite_eq_right hn]
    rw [heq, Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, zero_mul, add_zero,
      ENNReal.div_self (by exact_mod_cast s.positive.ne') (by finiteness), one_mul]

end

end SampLib.SplittingPPS
