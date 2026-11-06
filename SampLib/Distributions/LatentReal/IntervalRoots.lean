module

public import SampLib.Distributions.LatentReal.Interval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-! # Root bounds used by the lazy bisection oracle

These are deterministic enclosure facts. Termination of comparisons at a
particular law still requires almost-sure separation from tested thresholds.
-/

namespace SampLib.LatentReal

noncomputable section

/-- Nonnegative real `n`-th root, used only with a positive degree. -/
def root (n : ℕ) (x : ℝ) : ℝ := x ^ (n : ℝ)⁻¹

theorem root_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ root n x :=
  Real.rpow_nonneg hx _

theorem root_pow {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    root n x ^ n = x :=
  Real.rpow_inv_natCast_pow hx hn

/-- A comparison against a rational power is the same comparison against the root. -/
theorem below_root_iff {n : ℕ} (hn : n ≠ 0) {x bound : ℝ}
    (hx : 0 ≤ x) (hb : 0 ≤ bound) :
    x < bound ^ n ↔ root n x < bound := by
  simpa only [root_pow hn hx] using
    (pow_lt_pow_iff_left₀ (root_nonneg n hx) hb hn)

/-- Doubling an upper bracket eventually crosses every finite nonnegative source. -/
theorem exists_doubling_bracket {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    ∃ k : ℕ, x < ((2 : ℝ) ^ k) ^ n := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (root n x) (show (1 : ℝ) < 2 by norm_num)
  exact ⟨k, (below_root_iff hn hx (by positivity)).mpr hk⟩

namespace RationalInterval

/-- Bisection's power bracket encloses the unique nonnegative root. -/
theorem contains_root (interval : RationalInterval) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ interval.lowerReal)
    (hlo : interval.lowerReal ^ n ≤ x) (hhi : x ≤ interval.upperReal ^ n) :
    interval.Contains (root n x) := by
  have hu := hl.trans interval.lowerReal_le_upperReal
  constructor
  · apply (pow_le_pow_iff_left₀ hl (root_nonneg n hx) hn).mp
    rwa [root_pow hn hx]
  · apply (pow_le_pow_iff_left₀ (root_nonneg n hx) hu hn).mp
    rwa [root_pow hn hx]

/-- Stopping at adjacent integer bounds gives one denominator unit of uncertainty. -/
theorem width_le_inv_denominator (interval : RationalInterval)
    (hgap : interval.upper - interval.lower ≤ 1) :
    interval.width ≤ 1 / (interval.denominator : ℝ) := by
  dsimp [width, upperReal, lowerReal]
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hgap)
    interval.denominatorReal_pos.le

end RationalInterval

end

end SampLib.LatentReal
