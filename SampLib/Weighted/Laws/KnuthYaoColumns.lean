import SampLib.Discrete.WeightedChoice

/-! # Exact binary columns and live ranks

At depth `d`, each row has emitted `floor(2^d w/T)` leaves. The unrevealed
fractional rows sum to the integer number of live ranks. Doubling those ranks
pays the next column's leaves and leaves precisely the next live ranks.
-/

open Finset

namespace SampLib.KnuthYaoColumns

noncomputable section

variable {n : ℕ} (w : Fin n → ℕ) (T : ℕ)

def quotient (d : ℕ) (i : Fin n) : ℕ := 2 ^ d * w i / T

def remainder (d : ℕ) (i : Fin n) : ℕ := 2 ^ d * w i % T

def column (d : ℕ) (i : Fin n) : ℕ := quotient w T (d + 1) i % 2

def alive (d : ℕ) : ℕ := 2 ^ d - ∑ i, quotient w T d i

theorem column_lt_two (d : ℕ) (i : Fin n) : column w T d i < 2 := Nat.mod_lt _ (by omega)

/-- Halving the next quotient recovers the current quotient. -/
theorem quotient_half (d : ℕ) (i : Fin n) :
    quotient w T (d + 1) i / 2 = quotient w T d i := by
  unfold quotient
  rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [show 2 ^ d * 2 * w i = (2 ^ d * w i) * 2 by ring]
  exact Nat.mul_div_mul_right _ _ (by omega)

/-- The binary digit is exactly the increment in the doubled quotient. -/
theorem quotient_succ (d : ℕ) (i : Fin n) :
    quotient w T (d + 1) i = 2 * quotient w T d i + column w T d i := by
  have h := Nat.mod_add_div (quotient w T (d + 1) i) 2
  rw [quotient_half] at h
  dsimp [column]
  omega

/-- The same digit pays the difference between the two fractional remainders. -/
theorem remainder_succ (d : ℕ) (i : Fin n) :
    2 * remainder w T d i = T * column w T d i + remainder w T (d + 1) i := by
  have h₀ := Nat.mod_add_div (2 ^ d * w i) T
  have h₁ := Nat.mod_add_div (2 ^ (d + 1) * w i) T
  change remainder w T d i + T * quotient w T d i = 2 ^ d * w i at h₀
  change remainder w T (d + 1) i + T * quotient w T (d + 1) i =
    2 ^ (d + 1) * w i at h₁
  rw [quotient_succ, pow_succ] at h₁
  nlinarith

variable {w T} (hT : 0 < T) (htotal : ∑ i, w i = T)

include htotal

/-- Summing Euclidean division across all rows preserves the exact integer total. -/
theorem sum_division (d : ℕ) :
    (∑ i, remainder w T d i) + T * (∑ i, quotient w T d i) = T * 2 ^ d := by
  rw [mul_sum, ← sum_add_distrib]
  calc
    _ = ∑ i, 2 ^ d * w i := by
      apply sum_congr rfl
      intro i _
      exact Nat.mod_add_div _ _
    _ = T * 2 ^ d := by rw [← mul_sum, htotal, mul_comm]

include hT

theorem sum_quotient_le (d : ℕ) : ∑ i, quotient w T d i ≤ 2 ^ d := by
  have h := sum_division htotal d
  exact Nat.le_of_mul_le_mul_left (by omega) hT

/-- Every live rank carries exactly one denominator's worth of fractional row mass. -/
theorem sum_remainder (d : ℕ) : ∑ i, remainder w T d i = T * alive w T d := by
  have h := sum_division htotal d
  have ha : alive w T d + (∑ i, quotient w T d i) = 2 ^ d :=
    Nat.sub_add_cancel (sum_quotient_le hT htotal d)
  nlinarith

/-- There are fewer live ranks than rows, independently of the current depth. -/
theorem alive_lt (d : ℕ) : alive w T d < n := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    simp at htotal
    omega
  have hr : (∑ i, remainder w T d i) < n * T := by
    calc
      _ < ∑ _ : Fin n, T := sum_lt_sum
        (fun i _ => (Nat.mod_lt _ hT).le)
        ⟨⟨0, hn⟩, mem_univ _, Nat.mod_lt _ hT⟩
      _ = n * T := by simp
  rw [sum_remainder hT htotal] at hr
  nlinarith

/-- Twice the current live ranks split into this column's leaves and the next live ranks. -/
theorem alive_succ (d : ℕ) :
    2 * alive w T d = (∑ i, column w T d i) + alive w T (d + 1) := by
  have ha : alive w T d + (∑ i, quotient w T d i) = 2 ^ d :=
    Nat.sub_add_cancel (sum_quotient_le hT htotal d)
  have hb : alive w T (d + 1) + (∑ i, quotient w T (d + 1) i) = 2 ^ (d + 1) :=
    Nat.sub_add_cancel (sum_quotient_le hT htotal (d + 1))
  simp_rw [quotient_succ] at hb
  rw [sum_add_distrib, ← mul_sum, pow_succ] at hb
  omega

omit hT htotal

/-- The integer part vanishes precisely in the non-certain branch used by the source. -/
theorem alive_zero (hproper : ∀ i, w i < T) : alive w T 0 = 1 := by
  simp [alive, quotient, Nat.div_eq_of_lt (hproper _)]

end

end SampLib.KnuthYaoColumns
