module

public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

@[expose] public section

/-! # Dyadic groups of categorical ranks

The source groups one-based ranks into `[2^k,min(n,2^(k+1)-1)]`.
Their zero-based cutoffs are consecutive, so finite sums telescope without
requiring cancellation in the continuation's additive monoid.
-/

open Finset

namespace SampLib.DyadicGroups

def lower (k : ℕ) : ℕ := 2 ^ k
def upper (n k : ℕ) : ℕ := min n (2 ^ (k + 1) - 1)
def width (n k : ℕ) : ℕ := upper n k - lower k + 1

/-- Number of zero-based labels preceding group `k`. -/
def cutoff (n k : ℕ) : ℕ := min n (2 ^ k - 1)

theorem lower_pos (k : ℕ) : 0 < lower k := pow_pos (by decide) _

theorem lower_le_upper (n k : ℕ) (hk : k < n.size) : lower k ≤ upper n k := by
  have hn := Nat.lt_size.mp hk
  have hp := lower_pos k
  unfold lower upper at *
  rw [pow_succ]
  exact le_min hn (by omega)

theorem upper_le (n k : ℕ) : upper n k ≤ n := min_le_left _ _

theorem width_pos (n k : ℕ) : 0 < width n k := Nat.succ_pos _

theorem offset_lt (n k r : ℕ) (hk : k < n.size) (hr : r < width n k) :
    lower k - 1 + r < n := by
  have hl := lower_pos k
  have hle := lower_le_upper n k hk
  have hu := upper_le n k
  unfold width at hr
  omega

theorem cutoff_zero (n : ℕ) : cutoff n 0 = 0 := by simp [cutoff]

theorem cutoff_end (n : ℕ) : cutoff n n.size = n := by
  have hn := Nat.lt_size_self n
  exact min_eq_left (by omega)

theorem cutoff_mono (n : ℕ) : Monotone (cutoff n) := by
  intro i j hij
  exact min_le_min_left n (Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by decide) hij) 1)

theorem cutoff_lower (n k : ℕ) (hk : k < n.size) : cutoff n k = lower k - 1 := by
  have hn := Nat.lt_size.mp hk
  exact min_eq_right (by omega)

theorem cutoff_succ (n k : ℕ) : cutoff n (k + 1) = upper n k := rfl

theorem width_eq_cutoff (n k : ℕ) (hk : k < n.size) :
    width n k = cutoff n (k + 1) - cutoff n k := by
  rw [cutoff_lower n k hk, cutoff_succ]
  have hl := lower_pos k
  have hle := lower_le_upper n k hk
  unfold width
  omega

section sums

variable {A : Type*} [AddCommMonoid A]

/-- One source group occupies exactly the interval between successive cutoffs. -/
theorem sum_group (n k : ℕ) (hk : k < n.size) (F : ℕ → A) :
    (∑ r ∈ range (width n k), F (lower k - 1 + r)) =
      ∑ i ∈ Ico (cutoff n k) (cutoff n (k + 1)), F i := by
  rw [sum_Ico_eq_sum_range, ← width_eq_cutoff n k hk, cutoff_lower n k hk]

/-- Successive groups concatenate their finite intervals, including a truncated last group. -/
theorem sum_groups_prefix (n h : ℕ) (hh : h ≤ n.size) (F : ℕ → A) :
    (∑ k ∈ range h, ∑ r ∈ range (width n k), F (lower k - 1 + r)) =
      ∑ i ∈ range (cutoff n h), F i := by
  revert hh
  induction h with
  | zero => intro _; simp [cutoff_zero]
  | succ h ih =>
    intro hh
    rw [sum_range_succ, ih (by omega), sum_group n h (by omega)]
    exact sum_range_add_sum_Ico F (cutoff_mono n (Nat.le_succ h))

/-- Every categorical label occurs once, in its original rank order. -/
theorem sum_groups (n : ℕ) (F : ℕ → A) :
    (∑ k ∈ range n.size, ∑ r ∈ range (width n k), F (lower k - 1 + r)) =
      ∑ i ∈ range n, F i := by
  simpa only [cutoff_end] using sum_groups_prefix n n.size le_rfl F

end sums

end SampLib.DyadicGroups
