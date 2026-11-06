module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! # The central envelope for half-binomial rejection

The central coefficient bound follows directly from its exact recurrence.
Together with the integer square-root width, it pays for the proposal's
constant-height central block without Stirling's formula.
-/

namespace SampLib.BinomialHalfEnvelope

noncomputable section

/-- The exact block width used by the source sampler. -/
def width (n : ℕ) : ℕ := Nat.sqrt n + 1

theorem width_pos (n : ℕ) : 0 < width n := Nat.succ_pos _

theorem one_le_width (n : ℕ) : 1 ≤ width n := width_pos n

/-- A recurrence proof of the central `1 / sqrt(m+1)` decay. -/
theorem central_squared_bound (m : ℕ) :
    (m + 1 : ℝ) * (Nat.centralBinom m : ℝ) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => norm_num
  | succ m IH =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hm : (0 : ℝ) < m + 1 := by positivity
    have hrec : (m + 1 : ℝ) * (Nat.centralBinom (m + 1) : ℝ) =
        2 * (2 * m + 1) * (Nat.centralBinom m : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hsquare : (m + 1 : ℝ) ^ 2 * (Nat.centralBinom (m + 1) : ℝ) ^ 2 =
        (2 * (2 * m + 1) : ℝ) ^ 2 * (Nat.centralBinom m : ℝ) ^ 2 := by
      rw [← mul_pow, hrec, mul_pow]
    have hslack : (m + 1 + 1 : ℝ) * (2 * (2 * m + 1) : ℝ) ^ 2 ≤
        16 * (m + 1 : ℝ) ^ 3 := by nlinarith
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hm)).mp
    calc
      _ = (m + 1 + 1 : ℝ) * (2 * (2 * m + 1) : ℝ) ^ 2 *
          (Nat.centralBinom m : ℝ) ^ 2 := by rw [mul_left_comm, hsquare]; ring
      _ ≤ 16 * (m + 1 : ℝ) ^ 3 * (Nat.centralBinom m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hslack (sq_nonneg _)
      _ = 16 * (m + 1 : ℝ) ^ 2 * ((m + 1) * (Nat.centralBinom m : ℝ) ^ 2) := by ring
      _ ≤ 16 * (m + 1 : ℝ) ^ 2 * 16 ^ m :=
        mul_le_mul_of_nonneg_left IH (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem width_squared_bound (m : ℕ) : (width (2 * m) : ℝ) ^ 2 ≤ 16 * (m + 1 : ℝ) := by
  have hs : (Nat.sqrt (2 * m) : ℝ) ^ 2 ≤ 2 * m := by
    exact_mod_cast Nat.sqrt_le' (2 * m)
  unfold width
  push_cast
  nlinarith [sq_nonneg ((Nat.sqrt (2 * m) : ℝ) - 1)]

/-- A whole central block fits below the sampler's unnormalized envelope. -/
theorem central_envelope (m : ℕ) :
    (Nat.centralBinom m : ℝ) * width (2 * m) ≤ 4 * (2 : ℝ) ^ (2 * m) := by
  have hp : (4 * (2 : ℝ) ^ (2 * m)) ^ 2 = 16 * 16 ^ m := by
    calc
      _ = 16 * ((4 : ℝ) ^ m) ^ 2 := by rw [mul_pow, pow_mul]; norm_num
      _ = _ := by rw [← pow_mul, Nat.mul_comm m 2, pow_mul]; norm_num
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _ = (width (2 * m) : ℝ) ^ 2 * (Nat.centralBinom m : ℝ) ^ 2 := by ring
    _ ≤ 16 * (m + 1 : ℝ) * (Nat.centralBinom m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (width_squared_bound m) (sq_nonneg _)
    _ = 16 * ((m + 1 : ℝ) * (Nat.centralBinom m : ℝ) ^ 2) := by ring
    _ ≤ 16 * 16 ^ m := mul_le_mul_of_nonneg_left (central_squared_bound m) (by norm_num)
    _ = _ := hp.symm

end

end SampLib.BinomialHalfEnvelope
