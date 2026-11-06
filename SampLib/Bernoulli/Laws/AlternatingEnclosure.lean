module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Group.Nat.Even

@[expose] public section

/-! # Nested enclosures of an alternating series

A nonincreasing nonnegative coefficient sequence gives nested neighboring partial
sums. The enclosure at index zero is `[0,a 0]`, matching threshold samplers.
-/

open Finset Filter
open scoped Topology

namespace SampLib.AlternatingEnclosure

noncomputable section

def sign (n : ℕ) : ℝ := if n % 2 = 0 then 1 else -1

def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range (n + 1), sign j * a j

def lower (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then partialSum a n - a n else partialSum a n

def upper (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then partialSum a n else partialSum a n + a n

@[simp] theorem partial_zero (a : ℕ → ℝ) : partialSum a 0 = a 0 := by simp [partialSum, sign]

@[simp] theorem lower_zero (a : ℕ → ℝ) : lower a 0 = 0 := by simp [lower]

@[simp] theorem upper_zero (a : ℕ → ℝ) : upper a 0 = a 0 := by simp [upper]

theorem sign_eq (n : ℕ) : sign n = (-1 : ℝ) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · simp [sign, Nat.even_iff.mp h, h.neg_one_pow]
  · simp [sign, Nat.odd_iff.mp h, h.neg_one_pow]

theorem partial_succ (a : ℕ → ℝ) (n : ℕ) :
    partialSum a (n + 1) = partialSum a n + sign (n + 1) * a (n + 1) := by
  exact sum_range_succ _ _

theorem width (a : ℕ → ℝ) (n : ℕ) : upper a n - lower a n = a n := by
  unfold lower upper
  split_ifs <;> ring

/-- Adjacent partial-sum enclosures nest whenever the coefficients decrease. -/
theorem nested (a : ℕ → ℝ) (ha : Antitone a) (n : ℕ) :
    lower a n ≤ lower a (n + 1) ∧ upper a (n + 1) ≤ upper a n := by
  have h := ha (Nat.le_succ n)
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn' : (n + 1) % 2 = 1 := by omega
    simp only [lower, upper, hn, hn', sign, partial_succ, ite_true,
      one_ne_zero, ite_false, neg_one_mul]
    constructor <;> linarith
  · have hn' : (n + 1) % 2 = 0 := by omega
    simp only [lower, upper, hn, hn', sign, partial_succ, ite_true,
      one_ne_zero, ite_false, one_mul]
    constructor <;> linarith

theorem lower_mono (a : ℕ → ℝ) (ha : Antitone a) : Monotone (lower a) :=
  monotone_nat_of_le_succ (fun n => (nested a ha n).1)

theorem upper_anti (a : ℕ → ℝ) (ha : Antitone a) : Antitone (upper a) :=
  antitone_nat_of_succ_le (fun n => (nested a ha n).2)

theorem partial_mem (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    lower a n ≤ partialSum a n ∧ partialSum a n ≤ upper a n := by
  unfold lower upper
  split_ifs <;> constructor <;> linarith [ha n]

/-- Every later partial sum lies in the current enclosure. -/
theorem future_mem (a : ℕ → ℝ) (ha : Antitone a) (hpos : ∀ n, 0 ≤ a n)
    (n k : ℕ) (hnk : n ≤ k) :
    lower a n ≤ partialSum a k ∧ partialSum a k ≤ upper a n := by
  exact ⟨(lower_mono a ha hnk).trans (partial_mem a hpos k).1,
    (partial_mem a hpos k).2.trans (upper_anti a ha hnk)⟩

/-- The limit belongs to every enclosure as well. -/
theorem limit_mem (a : ℕ → ℝ) (ha : Antitone a) (hpos : ∀ n, 0 ≤ a n)
    (hs : Summable a) (n : ℕ) :
    lower a n ≤ ∑' j, sign j * a j ∧ (∑' j, sign j * a j) ≤ upper a n := by
  have ht₀ := hs.alternating.hasSum.tendsto_sum_nat
  have hn : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
    tendsto_atTop_mono Nat.le_succ tendsto_id
  have ht : Tendsto (partialSum a) atTop (𝓝 (∑' j, sign j * a j)) := by
    convert ht₀.comp hn using 1
    · ext k
      simp only [partialSum, Function.comp_apply, sign_eq]
    · simp only [sign_eq]

  constructor
  · apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with k hk using (future_mem a ha hpos n k hk).1
  · apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with k hk using (future_mem a ha hpos n k hk).2

end

end SampLib.AlternatingEnclosure
