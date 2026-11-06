module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # Binary digit sums and the even/odd partition -/

namespace SampLib.BinaryDigits

/-- Number of set bits in the ordinary binary expansion. -/
def weight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp] theorem weight_zero : weight 0 = 0 := by simp [weight]

/-- Removing the low bit leaves the other binary digits unchanged. -/
theorem weight_step (n : ℕ) (hn : 0 < n) :
    weight n = weight (n / 2) + n % 2 := by
  rw [weight, Nat.digits_of_two_le_of_pos (by decide) hn, List.sum_cons]
  exact Nat.add_comm _ _

@[simp] theorem weight_even (n : ℕ) : weight (2 * n) = weight n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [weight_step _ (by omega), show 2 * n / 2 = n by omega,
      show 2 * n % 2 = 0 by omega, Nat.add_zero]

@[simp] theorem weight_odd (n : ℕ) : weight (2 * n + 1) = weight n + 1 := by
  rw [weight_step _ (by omega), show (2 * n + 1) / 2 = n by omega,
    show (2 * n + 1) % 2 = 1 by omega]

/-- Pair consecutive ranks by their common high bits. -/
theorem sum_pairs {α : Type _} [AddCommMonoid α] (n : ℕ) (F : ℕ → α) :
    ∑ k ∈ Finset.range (2 * n), F k =
      ∑ k ∈ Finset.range n, (F (2 * k) + F (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp [Finset.sum_range_succ]

end SampLib.BinaryDigits
