module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic

@[expose] public section

/-! # A Wallis-type bound for the padded central binomial ratio

The square of the central coefficient, multiplied by its index, grows at least
sixteenfold every two indices. Telescoping this estimate gives the factor two
needed by the minimum-complement rejection coefficient when `2m ≤ 3r`.
-/

namespace SampLib.MinimumComplement

noncomputable section

/-- The largest binomial coefficient in row `n`. -/
def middle (n : ℕ) : ℕ := n.choose (n / 2)

private theorem middle_even (n : ℕ) : middle (2 * n) = Nat.centralBinom n := by
  simp [middle, Nat.centralBinom]

private theorem even_step (n : ℕ) :
    (n + 1) * middle (2 * n + 2) = 2 * (2 * n + 1) * middle (2 * n) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, middle_even, middle_even]
  exact Nat.succ_mul_centralBinom_succ n

private theorem odd_step (n : ℕ) :
    (n + 2) * middle (2 * n + 3) = 2 * (2 * n + 3) * middle (2 * n + 1) := by
  have hc : (2 * n + 2).choose (n + 1) = 2 * (2 * n + 1).choose n := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.choose_succ_succ]
    have hs := Nat.choose_symm (by omega : n ≤ 2 * n + 1)
    rw [show 2 * n + 1 - n = n + 1 by omega] at hs
    rw [hs]
    omega
  have h := Nat.choose_mul_succ_eq (2 * n + 2) (n + 1)
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by omega,
    show 2 * n + 3 - (n + 1) = n + 2 by omega, hc] at h
  simp only [middle, show (2 * n + 3) / 2 = n + 1 by omega,
    show (2 * n + 1) / 2 = n by omega]
  nlinarith [h]

private theorem even_growth (n : ℕ) :
    16 * ((2 * n : ℕ) : ℝ) * (middle (2 * n) : ℝ) ^ 2 ≤
      ((2 * n + 2 : ℕ) : ℝ) * (middle (2 * n + 2) : ℝ) ^ 2 := by
  have h : ((n : ℝ) + 1) * middle (2 * n + 2) =
      2 * (2 * (n : ℝ) + 1) * middle (2 * n) := by exact_mod_cast even_step n
  push_cast
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < (n : ℝ) + 1 by positivity)).mp
  nlinarith [congrArg (fun x : ℝ => x ^ 2) h, sq_nonneg (middle (2 * n) : ℝ)]

private theorem odd_growth (n : ℕ) :
    16 * ((2 * n + 1 : ℕ) : ℝ) * (middle (2 * n + 1) : ℝ) ^ 2 ≤
      ((2 * n + 3 : ℕ) : ℝ) * (middle (2 * n + 3) : ℝ) ^ 2 := by
  have h : ((n : ℝ) + 2) * middle (2 * n + 3) =
      2 * (2 * (n : ℝ) + 3) * middle (2 * n + 1) := by exact_mod_cast odd_step n
  push_cast
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos
    (show (0 : ℝ) < (n : ℝ) + 2 by positivity))).mp
  nlinarith [congrArg (fun x : ℝ => (2 * (n : ℝ) + 3) * x ^ 2) h,
    sq_nonneg (middle (2 * n + 1) : ℝ),
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg (middle (2 * n + 1) : ℝ))]

/-- A two-step Wallis estimate, uniform across the two parities. -/
theorem middle_two_step (n : ℕ) :
    16 * (n : ℝ) * (middle n : ℝ) ^ 2 ≤ (n + 2 : ℕ) * (middle (n + 2) : ℝ) ^ 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [show n = 2 * (n / 2) by omega]
    exact even_growth (n / 2)
  · rw [show n = 2 * (n / 2) + 1 by omega]
    simpa only [Nat.add_assoc] using odd_growth (n / 2)

/-- The adjacent-row estimates telescope without asymptotics or factorial bounds. -/
theorem middle_growth (r m : ℕ) :
    (16 : ℝ) ^ m * (middle r : ℝ) ^ 2 * r ≤
      (middle (r + 2 * m) : ℝ) ^ 2 * (r + 2 * m : ℕ) := by
  induction m with
  | zero => simp
  | succ m IH =>
    calc
      _ = 16 * ((16 : ℝ) ^ m * (middle r : ℝ) ^ 2 * r) := by rw [pow_succ]; ring
      _ ≤ 16 * ((middle (r + 2 * m) : ℝ) ^ 2 * (r + 2 * m : ℕ)) :=
        mul_le_mul_of_nonneg_left IH (by norm_num)
      _ ≤ _ := by
        have hindex : r + 2 * (m + 1) = r + 2 * m + 2 := by omega
        simp only [hindex]
        convert middle_two_step (r + 2 * m) using 1 <;> ring

/-- Padding of at least two thirds of `m` keeps the central acceptance ratio below one. -/
theorem central_acceptance_bound (m r : ℕ) (hr : 0 < r) (hpadding : 2 * m ≤ 3 * r) :
    (4 : ℝ) ^ m * middle r ≤ 2 * middle (r + 2 * m) := by
  have h := middle_growth r m
  have hpow : (16 : ℝ) ^ m = ((4 : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num
  rw [hpow] at h
  have hsum : (r + 2 * m : ℕ) ≤ 4 * r := by omega
  have hs := mul_le_mul_of_nonneg_left
    (show ((r + 2 * m : ℕ) : ℝ) ≤ 4 * r by exact_mod_cast hsum)
    (sq_nonneg (middle (r + 2 * m) : ℝ))
  have hsq : ((4 : ℝ) ^ m * middle r) ^ 2 ≤ (2 * (middle (r + 2 * m) : ℝ)) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < r by exact_mod_cast hr)).mp
    nlinarith [h.trans hs]
  nlinarith [show (0 : ℝ) ≤ (4 : ℝ) ^ m * middle r by positivity,
    show (0 : ℝ) ≤ (middle (r + 2 * m) : ℝ) by positivity]

end

end SampLib.MinimumComplement
