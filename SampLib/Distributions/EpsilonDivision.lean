import SampLib.LinearFactorySyntax
import SampLib.CoinComplement
import SampLib.Distributions.BernoulliRetry

/-! # Accepted and retried masses for epsilon division

The rational success mass is epsilon. A continued linear call retries with mass
1-p, leaving failure mass p-epsilon; normalization therefore gives epsilon/p.
-/

open ENNReal (ofReal ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.EpsilonDivision

noncomputable section

/-- The zero-numerator branch does not inspect its lower bound or input coin. -/
def Admissible (p : unitInterval) (a b lowerNum lowerDen : ℤ) : Prop :=
  0 ≤ a ∧ a < b ∧ 0 < lowerDen ∧ lowerNum ≤ lowerDen ∧
    (a ≠ 0 → 0 < lowerNum * b - a * lowerDen ∧ (lowerNum : ℝ) / lowerDen ≤ p)

abbrev selector (a b : ℤ) (ha : 0 ≤ a) (hab : a < b) :=
  RationalCoin.bias a b ha (by omega) hab.le

theorem selector_lt (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) :
    (selector a b h.1 h.2.1 : ℝ) < p := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_le_of_lt h.1 h.2.1)
  have hdR : (0 : ℝ) < lowerDen := by exact_mod_cast h.2.2.1
  obtain ⟨hm, hp⟩ := h.2.2.2.2 ha.ne'
  have hmR : (0 : ℝ) < lowerNum * b - a * lowerDen := by exact_mod_cast hm
  apply lt_of_lt_of_le _ hp
  exact (div_lt_div_iff₀ hbR hdR).mpr (by nlinarith)

theorem selector_le (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) : (selector a b h.1 h.2.1 : ℝ) ≤ p := by
  by_cases ha : a = 0
  · subst a
    simpa [selector, RationalCoin.bias] using p.2.1
  · exact (selector_lt p a b lowerNum lowerDen h (by have := h.1; omega)).le

theorem retry_lt_one (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) :
    (unitInterval.symm p : ℝ) < 1 := by
  have hp := lt_of_le_of_lt (selector a b h.1 h.2.1).2.1
    (selector_lt p a b lowerNum lowerDen h ha)
  rw [unitInterval.coe_symm_eq]
  linarith

/-- The intended ratio, with the real convention 0/0=0 on the unused zero branch. -/
def bias (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) : unitInterval :=
  BernoulliRetry.bias (selector a b h.1 h.2.1) ((p : ℝ) - selector a b h.1 h.2.1)
    (selector a b h.1 h.2.1).2.1 (sub_nonneg.mpr (selector_le p a b lowerNum lowerDen h))

@[simp] theorem bias_coe (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) :
    (bias p a b lowerNum lowerDen h : ℝ) = ((a : ℝ) / b) / p := by
  change ((a : ℝ) / b) / (((a : ℝ) / b) + ((p : ℝ) - (a : ℝ) / b)) = _
  congr 1
  ring

@[simp] theorem bias_zero (p : unitInterval) (b lowerNum lowerDen : ℤ)
    (h : Admissible p 0 b lowerNum lowerDen) : bias p 0 b lowerNum lowerDen h = 0 := by
  apply Subtype.ext
  simp [bias_coe]

theorem bias_full_lower (p : unitInterval) (a b lowerDen : ℤ)
    (h : Admissible p a b lowerDen lowerDen) (ha : 0 < a) :
    bias p a b lowerDen lowerDen h = selector a b h.1 h.2.1 := by
  have hd : (lowerDen : ℝ) ≠ 0 := by exact_mod_cast h.2.2.1.ne'
  have hp : (p : ℝ) = 1 := le_antisymm p.2.2
    (by simpa [hd] using (h.2.2.2.2 ha.ne').2)
  apply Subtype.ext
  simp [bias_coe, hp, selector, RationalCoin.bias]


def marginNum (a b lowerNum lowerDen : ℤ) : ℤ := lowerNum * b - a * lowerDen

def marginDen (a b lowerDen : ℤ) : ℤ := lowerDen * (b - a)

theorem linear_admissible (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen) :
    LinearFactory.Admissible (unitInterval.symm p) b (b - a)
      (marginNum a b lowerNum lowerDen) (marginDen a b lowerDen) := by
  have hb : 0 < b := lt_of_le_of_lt h.1 h.2.1
  have hba : 0 < b - a := sub_pos.mpr h.2.1
  obtain ⟨hm, hp⟩ := h.2.2.2.2 ha.ne'
  have hmd : marginNum a b lowerNum lowerDen < marginDen a b lowerDen := by
    dsimp [marginNum, marginDen]
    nlinarith [mul_pos hb (sub_pos.mpr hl)]
  refine ⟨hb.le, hba, fun _ => ⟨hm, hmd, ?_⟩⟩
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbaR : (0 : ℝ) < (b : ℝ) - a := by exact_mod_cast hba
  have hdR : (0 : ℝ) < lowerDen := by exact_mod_cast h.2.2.1
  have hid : 1 - (marginNum a b lowerNum lowerDen : ℝ) / marginDen a b lowerDen =
      (b : ℝ) * (1 - (lowerNum : ℝ) / lowerDen) / (b - a) := by
    simp only [marginNum, marginDen, Int.cast_sub, Int.cast_mul]
    field_simp
    ring
  rw [hid]
  simp only [Gambler.ratio, unitInterval.coe_symm_eq, Int.cast_sub]
  apply div_le_div_of_nonneg_right _ hbaR.le
  exact mul_le_mul_of_nonneg_left (by linarith) hbR.le

abbrev innerBias (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen) :=
  LinearFactory.bias (unitInterval.symm p) b (b - a)
    (marginNum a b lowerNum lowerDen) (marginDen a b lowerDen)
    (linear_admissible p a b lowerNum lowerDen h ha hl)

/-- The linear retry exactly cancels the rational coin's failure factor. -/
theorem retry_mass (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen) :
    (1 - (selector a b h.1 h.2.1 : ℝ)) * innerBias p a b lowerNum lowerDen h ha hl = 1 - p := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (lt_of_le_of_lt h.1 h.2.1).ne'
  have hbaR : (b : ℝ) - a ≠ 0 := by exact_mod_cast (sub_pos.mpr h.2.1).ne'
  simp only [selector, RationalCoin.bias, innerBias, LinearFactory.bias_coe,
    unitInterval.coe_symm_eq, Int.cast_sub]
  field_simp

def retryCredit (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (bias p a b lowerNum lowerDen h) F +
    BernoulliRetry.factor (unitInterval.symm p) * ε

def innerCredit (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (z : Bool) : ℝ≥0∞ :=
  if z then retryCredit p a b lowerNum lowerDen h F ε else F false

def selectorCredit (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (z : Bool) : ℝ≥0∞ :=
  if z then F true else RealCoin.credit (innerBias p a b lowerNum lowerDen h ha hl)
    (innerCredit p a b lowerNum lowerDen h F ε)

/-- Success, failure and retry masses are epsilon, p-epsilon and 1-p. -/
theorem expectation (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    RealCoin.credit (selector a b h.1 h.2.1)
      (selectorCredit p a b lowerNum lowerDen h ha hl F ε) ≤
        RealCoin.credit (bias p a b lowerNum lowerDen h) F + ε := by
  let r := selector a b h.1 h.2.1
  let t := innerBias p a b lowerNum lowerDen h ha hl
  let C := retryCredit p a b lowerNum lowerDen h F ε
  have ht : (1 - (r : ℝ)) * t = 1 - p := retry_mass p a b lowerNum lowerDen h ha hl
  have hf : (1 - (r : ℝ)) * (1 - (t : ℝ)) = (p : ℝ) - r := by nlinarith
  have hT : ofReal (1 - (r : ℝ)) * ofReal (t : ℝ) = ofReal (1 - (p : ℝ)) := by
    rw [← ofReal_mul (sub_nonneg.mpr r.2.2), ht]
  have hF : ofReal (1 - (r : ℝ)) * ofReal (1 - (t : ℝ)) = ofReal ((p : ℝ) - r) := by
    rw [← ofReal_mul (sub_nonneg.mpr r.2.2), hf]
  have hp : 0 < (p : ℝ) := lt_of_le_of_lt r.2.1 (selector_lt p a b lowerNum lowerDen h ha)
  have hb := sub_nonneg.mpr (selector_le p a b lowerNum lowerDen h)
  have hsum : (r : ℝ) + ((p : ℝ) - r) + (unitInterval.symm p : ℝ) = 1 := by
    rw [unitInterval.coe_symm_eq]
    ring
  calc
    _ = ofReal (r : ℝ) * F true + ofReal ((p : ℝ) - r) * F false +
        ofReal (1 - (p : ℝ)) * C := by
      change ofReal (r : ℝ) * F true + ofReal (1 - (r : ℝ)) *
        (ofReal (t : ℝ) * C + ofReal (1 - (t : ℝ)) * F false) = _
      rw [mul_add]
      simp only [← mul_assoc, hT, hF]
      ring
    _ ≤ _ := by
      simpa only [r, C, unitInterval.coe_symm_eq, bias, retryCredit] using
        BernoulliRetry.expectation (r : ℝ) ((p : ℝ) - r) r.2.1 hb (unitInterval.symm p)
          (by rw [unitInterval.coe_symm_eq]; linarith) hsum F ε

end

end SampLib.EpsilonDivision
