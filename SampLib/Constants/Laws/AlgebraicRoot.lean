import SampLib.Constants.Laws.BernoulliMean

/-! # Root cells and sign tests

A cell is a rational interval that contains the root. A fair bit picks a half-cell; the
sign at the midpoint tells which half holds the root.
-/

open Finset
open scoped ENNReal

namespace SampLib.AlgebraicRoot

noncomputable section

/-- A rational cell known to contain the target probability. -/
structure Cell (p : unitInterval) where
  index : ℕ
  scale : ℕ
  scale_pos : 0 < scale
  lower : (index : ℝ) ≤ (p : ℝ) * scale
  upper : (p : ℝ) * scale ≤ index + 1

namespace Cell

/-- Conditional probability after the preceding uniform bits selected this cell. -/
def probability {p : unitInterval} (c : Cell p) : unitInterval :=
  ⟨(p : ℝ) * c.scale - c.index, sub_nonneg.mpr c.lower, by linarith [c.upper]⟩

def initial (p : unitInterval) : Cell p :=
  ⟨0, 1, by decide, by simpa using p.2.1, by simpa using p.2.2⟩

def left {p : unitInterval} (c : Cell p) (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) : Cell p where
  index := 2 * c.index
  scale := 2 * c.scale
  scale_pos := by have := c.scale_pos; positivity
  lower := by have := c.lower; push_cast; nlinarith
  upper := by dsimp [probability] at h; push_cast; nlinarith

def right {p : unitInterval} (c : Cell p) (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) : Cell p where
  index := 2 * c.index + 1
  scale := 2 * c.scale
  scale_pos := by have := c.scale_pos; positivity
  lower := by dsimp [probability] at h; push_cast; nlinarith
  upper := by have := c.upper; push_cast; nlinarith

theorem left_probability {p : unitInterval} (c : Cell p)
    (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) :
    ((c.left h).probability : ℝ) = 2 * (c.probability : ℝ) := by
  dsimp [probability, left]
  push_cast
  ring

theorem right_probability {p : unitInterval} (c : Cell p)
    (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) :
    ((c.right h).probability : ℝ) = 2 * (c.probability : ℝ) - 1 := by
  dsimp [probability, right]
  push_cast
  ring

end Cell

/-- Credits for the two equally likely half-cells. A midpoint root decides at once. -/
def bitCredit {p : unitInterval} (c : Cell p) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (bit : ℕ) : ℝ≥0∞ :=
  if (c.probability : ℝ) = (2 : ℝ)⁻¹ then F (decide (bit = 0))
  else if h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹ then
    if bit = 0 then RealCoin.credit (c.left h).probability F + 2 * ε else F false
  else if bit = 0 then F true
    else RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε

private theorem left_mean {p : unitInterval} (c : Cell p)
    (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) :
    CoinMean.bias (c.left h).probability 0 = c.probability := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * 0 + (1 / 2 : ℝ) * ((c.left h).probability : ℝ) = _
  rw [Cell.left_probability]
  ring

private theorem right_mean {p : unitInterval} (c : Cell p)
    (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) :
    CoinMean.bias 1 (c.right h).probability = c.probability := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * ((c.right h).probability : ℝ) + (1 / 2 : ℝ) * 1 = _
  rw [Cell.right_probability]
  ring

private theorem credit_zero (F : Bool → ℝ≥0∞) : RealCoin.credit 0 F = F false := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem credit_one (F : Bool → ℝ≥0∞) : RealCoin.credit 1 F = F true := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem retry_credit (a b ε : ℝ≥0∞) :
    (a + 2 * ε + b) / 2 = (a + b) / 2 + ε := by
  rw [show a + 2 * ε + b = (a + b) + ε * 2 by ring,
    ENNReal.add_div, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- A half-cell is either deterministic or contains the rescaled root.
Their fair mixture has the original bias; the sole retry receives doubled slack. -/
theorem expectation {p : unitInterval} (c : Cell p) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    (∑ j ∈ range 2, bitCredit c F ε j) / 2 ≤
      RealCoin.credit c.probability F + ε := by
  simp only [sum_range_succ, sum_range_zero, zero_add]
  by_cases heq : (c.probability : ℝ) = (2 : ℝ)⁻¹
  · have hcredit : RealCoin.credit c.probability F = (F true + F false) / 2 := by
      norm_num [RealCoin.credit, RealCoin.pmf, heq, ENNReal.ofReal_inv_of_pos,
        ENNReal.ofReal_div_of_pos, ENNReal.div_eq_inv_mul]
      ring
    simp [bitCredit, heq, ← hcredit]
  · by_cases h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹
    · have hm := CoinMean.credit_mean (c.left h).probability 0 F
      rw [left_mean, credit_zero] at hm
      simp only [bitCredit, heq, h, dite_true, ite_false, ite_true, Nat.one_ne_zero]
      rw [retry_credit, hm]
    · have hm := CoinMean.credit_mean 1 (c.right (le_of_not_ge h)).probability F
      rw [right_mean, credit_one] at hm
      simp only [bitCredit, heq, h, dite_false, ite_false, ite_true, Nat.one_ne_zero]
      rw [show F true + (RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε) =
        RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε + F true by ring,
        retry_credit, add_comm (RealCoin.credit (c.right (le_of_not_ge h)).probability F), hm]

/-- The sign is fixed on each side of the root; `s` is its sign at zero. -/
def side (p : unitInterval) (s : ℤ) (n den : ℕ) : ℤ :=
  if (n : ℝ) < (p : ℝ) * den then s
  else if (p : ℝ) * den < n then -s else 0

private theorem middle_side {p : unitInterval} (c : Cell p) (s : ℤ) :
    side p s (2 * c.index + 1) (2 * c.scale) =
      if (c.probability : ℝ) < (2 : ℝ)⁻¹ then -s
      else if (2 : ℝ)⁻¹ < (c.probability : ℝ) then s else 0 := by
  have hl : ((2 * c.index + 1 : ℕ) : ℝ) < (p : ℝ) * (2 * c.scale : ℕ) ↔
      (2 : ℝ)⁻¹ < (c.probability : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [Cell.probability]
    constructor <;> intro h <;> linarith
  have hr : (p : ℝ) * (2 * c.scale : ℕ) < ((2 * c.index + 1 : ℕ) : ℝ) ↔
      (c.probability : ℝ) < (2 : ℝ)⁻¹ := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [Cell.probability]
    constructor <;> intro h <;> linarith
  simp only [side, hl, hr]
  by_cases h : (c.probability : ℝ) < (2 : ℝ)⁻¹
  · simp [h, not_lt.mpr (le_of_lt h)]
  · simp [h]

/-- The midpoint numerator stays within the denominator below one. -/
theorem midpoint_le_den {p : unitInterval} (hp : (p : ℝ) < 1) (c : Cell p) :
    2 * c.index + 1 ≤ 2 * c.scale := by
  have hscale : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  have hindex : (c.index : ℝ) < c.scale :=
    c.lower.trans_lt (by nlinarith)
  have : c.index < c.scale := by exact_mod_cast hindex
  omega

/-- A root at the midpoint gives sign zero there. -/
theorem middle_eq {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (c.probability : ℝ) = (2 : ℝ)⁻¹) :
    side p s (2 * c.index + 1) (2 * c.scale) = 0 := by
  simp [middle_side, h]

/-- A root left of the midpoint flips the sign there. -/
theorem middle_lt {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (c.probability : ℝ) < (2 : ℝ)⁻¹) :
    side p s (2 * c.index + 1) (2 * c.scale) = -s := by
  simp [middle_side, h]

/-- A root right of the midpoint keeps the sign there. -/
theorem middle_gt {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (2 : ℝ)⁻¹ < (c.probability : ℝ)) :
    side p s (2 * c.index + 1) (2 * c.scale) = s := by
  simp [middle_side, h, not_lt.mpr h.le]

/-- The sign at zero is `s`. -/
theorem side_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (s : ℤ) :
    side p s 0 1 = s := by simp [side, hp]

/-- The sign at one is `-s`. -/
theorem side_one (p : unitInterval) (hp : (p : ℝ) < 1) (s : ℤ) :
    side p s 1 1 = -s := by simp [side, hp, not_lt.mpr p.2.2]

end

end SampLib.AlgebraicRoot
