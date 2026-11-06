module

public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # The least enclosing binary word width -/

namespace SampLib.PowerOfTwoCeiling

/-- The least power of two containing a positive range. -/
def width (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

theorem le_width (n : ℕ) : n ≤ width n := Nat.le_pow_clog (by decide) n

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

instance (n : ℕ) : NeZero (width n) := ⟨(width_pos n).ne'⟩

theorem width_le_double (n : ℕ) (hn : 0 < n) : width n ≤ 2 * n := by
  by_cases h : n = 1
  · subst n
    norm_num [width]
  · have hn1 : 1 < n := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hn1
    have hp : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hprev := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn1
    simp only [Nat.pred_eq_sub_one] at hprev
    unfold width
    rw [hp]
    omega

end SampLib.PowerOfTwoCeiling
