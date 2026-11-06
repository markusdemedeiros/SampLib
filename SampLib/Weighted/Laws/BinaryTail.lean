module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

/-! # The mass of an infinite binary row

Discounting the actual bits gives a tail in the unit interval. Its one-step
recurrence and the scaled quotient identity expose the finite-prefix argument
without choosing a terminating expansion at the probability-one endpoint.
-/

namespace SampLib.BinaryTail

noncomputable section

/-- Remaining mass after the first `d` columns of a binary row. -/
def value (bits : ℕ → ℕ) (d : ℕ) : ℝ :=
  ∑' n : ℕ, (bits (d + n) : ℝ) * (1 / 2 : ℝ) ^ (n + 1)

private theorem geometric : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  convert (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left
    (1 / 2 : ℝ) using 1
  · funext n
    rw [pow_succ]
    ring
  · norm_num

theorem summable (bits : ℕ → ℕ) (hb : ∀ n, bits n ≤ 1) (d : ℕ) :
    Summable (fun n : ℕ => (bits (d + n) : ℝ) * (1 / 2 : ℝ) ^ (n + 1)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ geometric.summable
  intro n
  have h : (bits (d + n) : ℝ) ≤ 1 := by exact_mod_cast hb (d + n)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h
    (show 0 ≤ (1 / 2 : ℝ) ^ (n + 1) by positivity)

theorem nonneg (bits : ℕ → ℕ) (d : ℕ) : 0 ≤ value bits d :=
  tsum_nonneg (fun n => by positivity)

theorem le_one (bits : ℕ → ℕ) (hb : ∀ n, bits n ≤ 1) (d : ℕ) : value bits d ≤ 1 := by
  calc
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) :=
      (summable bits hb d).tsum_le_tsum (fun n => by
        have h : (bits (d + n) : ℝ) ≤ 1 := by exact_mod_cast hb (d + n)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h
          (show 0 ≤ (1 / 2 : ℝ) ^ (n + 1) by positivity))
        geometric.summable
    _ = 1 := geometric.tsum_eq

/-- One column spends its leading bit and halves the continuation's remaining mass. -/
theorem succ (bits : ℕ → ℕ) (hb : ∀ n, bits n ≤ 1) (d : ℕ) :
    2 * value bits d = (bits d : ℝ) + value bits (d + 1) := by
  unfold value
  rw [(summable bits hb d).tsum_eq_zero_add]
  simp only [Nat.add_zero]
  have hshift :
      (fun n : ℕ => (bits (d + (n + 1)) : ℝ) * (1 / 2 : ℝ) ^ (n + 1 + 1)) =
        (fun n : ℕ => ((bits ((d + 1) + n) : ℝ) * (1 / 2 : ℝ) ^ (n + 1)) * (1 / 2)) := by
    funext n
    rw [show d + (n + 1) = (d + 1) + n by omega, pow_succ]
    ring
  rw [hshift, (summable bits hb (d + 1)).tsum_mul_right]
  ring

/-- First-pass columns telescope against the integer's successive binary quotients. -/
theorem scaled_prefix (bits : ℕ → ℕ) (hb : ∀ n, bits n ≤ 1) (E k : ℕ)
    (hE : E < 2 ^ k)
    (hbits : ∀ c, c < k → bits c = E / 2 ^ (k - 1 - c) % 2)
    (c : ℕ) (hc : c ≤ k) :
    (2 : ℝ) ^ c * value bits 0 = (E / 2 ^ (k - c) : ℕ) + value bits c := by
  induction c with
  | zero => simp [Nat.div_eq_of_lt hE]
  | succ c ih =>
    have hck : c < k := by omega
    have hi := ih (by omega)
    have ht := succ bits hb c
    have hhalf : E / 2 ^ (k - (c + 1)) / 2 = E / 2 ^ (k - c) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [← pow_succ, show k - (c + 1) + 1 = k - c by omega]
    have hq := Nat.mod_add_div (E / 2 ^ (k - (c + 1))) 2
    rw [hhalf, show k - (c + 1) = k - 1 - c by omega, ← hbits c hck] at hq
    have hq' : (bits c : ℝ) + 2 * (E / 2 ^ (k - c) : ℕ) =
        (E / 2 ^ (k - (c + 1)) : ℕ) := by
      rw [show k - (c + 1) = k - 1 - c by omega]
      exact_mod_cast hq
    rw [pow_succ]
    nlinarith

end

end SampLib.BinaryTail
