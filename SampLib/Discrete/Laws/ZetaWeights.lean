import SampLib.Discrete.Laws.DyadicPower
import SampLib.Discrete.Laws.DyadicProposal
import SampLib.Common.Laws.RationalPower
import SampLib.Bernoulli.Laws.VonNeumann

/-! # Dyadic rejection leaves zeta weights

The geometric level weight cancels the block width raised to the target power.
Each positive integer is proposed once, leaving the same multiple of `k^(-a/b)`.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Zeta

noncomputable section

open DyadicBlocks

def exponent (a b : ℕ) : ℝ := (a : ℝ) / b

def tail (a b : ℕ) (hb : 0 < b) : unitInterval :=
  RationalPower.bias VonNeumann.fairBias (a - b) b hb

def bias (a b : ℕ) (hb : 0 < b) : unitInterval := unitInterval.symm (tail a b hb)

theorem exponent_gt_one (a b : ℕ) (hb : 0 < b) (hab : b < a) : 1 < exponent a b := by
  unfold exponent
  exact (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)

/-- The continuation probability is the dyadic power `2^(1-a/b)`. -/
theorem tail_eq (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    (tail a b hb : ℝ) = (2 : ℝ) ^ (1 - exponent a b) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  change (1 / 2 : ℝ) ^ (((a - b : ℕ) : ℝ) / b) = _
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  rw [Nat.cast_sub hab.le]
  unfold exponent
  rw [sub_div, div_self hbR]
  ring

theorem bias_pos (a b : ℕ) (hb : 0 < b) (hab : b < a) : 0 < (bias a b hb : ℝ) := by
  change 0 < 1 - (tail a b hb : ℝ)
  rw [tail_eq a b hb hab]
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have := exponent_gt_one a b hb hab; linarith)

theorem failure_eq (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    1 - (bias a b hb : ℝ) = (2 : ℝ) ^ (1 - exponent a b) := by
  simp only [bias, unitInterval.coe_symm_eq, sub_sub_cancel, tail_eq a b hb hab]

/-- Block start divided by its positive candidate. -/
def ratio (t : Block) : unitInterval :=
  ⟨(2 : ℝ) ^ t.1 / (value t : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast value_pos t)).mpr
      exact_mod_cast (show 2 ^ t.1 ≤ value t by unfold value; omega)⟩

def acceptance (a b : ℕ) (hb : 0 < b) (t : Block) : unitInterval :=
  RationalPower.bias (ratio t) a b hb

def proposal (a b : ℕ) (hb : 0 < b) : Measure Block := DyadicProposal.law (bias a b hb)

instance (a b : ℕ) (hb : 0 < b) : IsProbabilityMeasure (proposal a b hb) := by
  unfold proposal
  infer_instance

/-- Accepted point masses lose their dyadic level and rank factors. -/
theorem accepted_atom (a b : ℕ) (hb : 0 < b) (hab : b < a) (t : Block) :
    ENNReal.ofReal (acceptance a b hb t : ℝ) * proposal a b hb {t} =
      ENNReal.ofReal (bias a b hb : ℝ) *
        ENNReal.ofReal ((value t : ℝ) ^ (-exponent a b)) := by
  have hp : bias a b hb ≠ 0 := by
    intro h
    have := bias_pos a b hb hab
    simp [h] at this
  rw [proposal, DyadicProposal.law_singleton_ofReal _ hp,
    ← ENNReal.ofReal_mul (acceptance a b hb t).2.1,
    ← ENNReal.ofReal_mul (bias a b hb).2.1]
  congr 1
  change (((2 : ℝ) ^ t.1) / (value t : ℝ)) ^ exponent a b *
    (((1 - (bias a b hb : ℝ)) ^ t.1 * bias a b hb) / (2 : ℝ) ^ t.1) = _
  rw [failure_eq a b hb hab]
  calc
    _ = (bias a b hb : ℝ) *
        ((((2 : ℝ) ^ (1 - exponent a b)) ^ t.1 / (2 : ℝ) ^ t.1) *
          (((2 : ℝ) ^ t.1) / (value t : ℝ)) ^ exponent a b) := by ring
    _ = _ := by
      rw [DyadicBlocks.cancellation _ _ _ (by exact_mod_cast value_pos t)]

end

end SampLib.Zeta
