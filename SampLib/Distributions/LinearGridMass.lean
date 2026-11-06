module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact mass of an integer-grid linear profile -/

namespace SampLib.LinearGridMass

/-- Gauss' sum computes twice the half-open interpolated density mass. -/
theorem twice_sum (w ha hb : ℕ) (hw : 0 < w) :
    2 * (Finset.sum (Finset.range w) (fun k => ha * (w - k) + hb * k)) =
      w * ((w + 1) * ha + (w - 1) * hb) := by
  let S := Finset.sum (Finset.range w) (fun k => k)
  let T := Finset.sum (Finset.range w) (fun k => w - k)
  have hpart : S + T = w * w := by
    dsimp [S, T]
    rw [← Finset.sum_add_distrib]
    calc
      _ = Finset.sum (Finset.range w) (fun _ => w) :=
        Finset.sum_congr rfl fun k hk => Nat.add_sub_of_le (Finset.mem_range.mp hk).le
      _ = w * w := by simp [nsmul_eq_mul]
  have hs : S * 2 = w * (w - 1) := Finset.sum_range_id_mul_two w
  have hpred : w * (w - 1) + w = w * w := by
    simpa [Nat.mul_add] using congrArg (fun x => w * x) (Nat.sub_add_cancel hw)
  have ht : 2 * T = w * (w + 1) := by nlinarith only [hpart, hs, hpred]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change 2 * (ha * T + hb * S) = _
  calc
    _ = ha * (2 * T) + hb * (S * 2) := by ring
    _ = ha * (w * (w + 1)) + hb * (w * (w - 1)) := by rw [ht, hs]
    _ = _ := by ring

end SampLib.LinearGridMass
