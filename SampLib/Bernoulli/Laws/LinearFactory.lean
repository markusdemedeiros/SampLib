import SampLib.Bernoulli.Laws.LinearFactoryParameters
import SampLib.Bernoulli.Laws.LinearFactoryInner
import SampLib.Uniform.Laws.RationalCoin

/-! # The adaptive linear factory

The expected number of recursive factory calls is bounded by the supplied margin. This
makes the adaptive recursion subcritical without a well-founded order on the margins.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal BigOperators

namespace SampLib.LinearFactory

noncomputable section

private abbrev S (t : unitInterval) (n : ℕ) : ℝ := FiniteGeometricWalk.total (t : ℝ) n

namespace Parameters

variable {p : unitInterval}

/-- Integer-to-natural transport for the finite walk's height. -/
def height (σ : Parameters p) : ℕ := (scale σ.e σ.f).toNat

theorem height_cast (σ : Parameters p) (h : σ.b < σ.a) :
    ((σ.height : ℕ) : ℤ) = scale σ.e σ.f :=
  Int.toNat_of_nonneg (σ.scale_pos h).le

theorem height_two (σ : Parameters p) (h : σ.b < σ.a) : 2 ≤ σ.height := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  have hm := (scale_bounds σ.e σ.f he hef).1
  exact_mod_cast (show (2 : ℤ) ≤ (σ.height : ℤ) by rw [σ.height_cast h]; exact hm)

theorem height_real (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.height : ℝ) = (scale σ.e σ.f : ℝ) := by exact_mod_cast σ.height_cast h

theorem selector_bounds (σ : Parameters p) (h : σ.b < σ.a) :
    0 ≤ scale σ.e σ.f - 1 ∧ 0 < scale σ.e σ.f ∧ scale σ.e σ.f - 1 ≤ scale σ.e σ.f := by
  have hm := σ.scale_pos h
  omega

/-- Rational selector used after the outer walk succeeds. -/
def selector (σ : Parameters p) (h : σ.b < σ.a) : unitInterval :=
  RationalCoin.bias (scale σ.e σ.f - 1) (scale σ.e σ.f)
    (σ.selector_bounds h).1 (σ.selector_bounds h).2.1 (σ.selector_bounds h).2.2

@[simp] theorem selector_coe (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.selector h : ℝ) = ((σ.height : ℝ) - 1) / σ.height := by
  simp only [selector, RationalCoin.bias, Int.cast_sub, Int.cast_one, σ.height_real h]

theorem selector_complement (σ : Parameters p) (h : σ.b < σ.a) :
    1 - (σ.selector h : ℝ) = 1 / (scale σ.e σ.f : ℝ) := by
  have hm : (scale σ.e σ.f : ℝ) ≠ 0 := by exact_mod_cast (σ.scale_pos h).ne'
  rw [selector_coe, σ.height_real h]
  field_simp
  ring

/-- The normalized lower-exit law of the outer walk. -/
def walkBias (σ : Parameters p) (h : σ.b < σ.a) : unitInterval :=
  Gambler.bias p (σ.next h).a (σ.next h).b (σ.next_a_pos h)
    (σ.next h).admissible.2.1 σ.height

private theorem tail_one (t : unitInterval) (N : ℕ) :
    FiniteGeometricWalk.tail (t : ℝ) N 1 = (t : ℝ) * S t (N - 1) := by
  simp [FiniteGeometricWalk.tail, Finset.sum_Ico_eq_sum_range,
    pow_add, S, FiniteGeometricWalk.total, Finset.mul_sum]

theorem walkBias_coe (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.walkBias h : ℝ) = ((σ.next h).bias : ℝ) *
      S (σ.next h).bias (σ.height - 1) / S (σ.next h).bias σ.height := by
  have hm : 1 ≤ σ.height := le_trans (by norm_num) (σ.height_two h)
  change FiniteGeometricWalk.tail ((σ.next h).bias : ℝ) (max σ.height 1) 1 /
    S (σ.next h).bias (max σ.height 1) = _
  rw [max_eq_left hm, tail_one]

theorem bias_from_next (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.bias : ℝ) = ((σ.next h).bias : ℝ) * ((σ.height : ℝ) - 1) / σ.height := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  have hm := (scale_bounds σ.e σ.f he hef).1
  have hn := σ.next_ratio h
  change ((σ.next h).bias : ℝ) =
    (σ.bias : ℝ) * (scale σ.e σ.f : ℝ) / ((scale σ.e σ.f : ℝ) - 1) at hn
  have hm0 : (scale σ.e σ.f : ℝ) ≠ 0 := by exact_mod_cast (σ.scale_pos h).ne'
  have hm1 : (scale σ.e σ.f : ℝ) - 1 ≠ 0 := by
    exact_mod_cast (show scale σ.e σ.f - 1 ≠ 0 by omega)
  rw [σ.height_real h]
  field_simp at hn ⊢
  linarith

/-- The walk, rational gate, and inner loop compose to the requested linear bias. -/
theorem outer_bias (σ : Parameters p) (h : σ.b < σ.a) :
    CoinConditional.bias
      (CoinConditional.bias 1 (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h))
      0 (σ.walkBias h) = σ.bias := by
  let t := (σ.next h).bias
  have hM := σ.height_two h
  have hp : 0 < σ.height - 1 := by omega
  have hSM := FiniteGeometricWalk.total_pos (t : ℝ) t.2.1 σ.height (by omega)
  have hSp := FiniteGeometricWalk.total_pos (t : ℝ) t.2.1 (σ.height - 1) hp
  have hS : S t σ.height = S t (σ.height - 1) + (t : ℝ) ^ (σ.height - 1) := by
    simpa only [S, FiniteGeometricWalk.total,
      Nat.sub_add_cancel (show 1 ≤ σ.height by omega)] using
      Finset.sum_range_succ (fun j => (t : ℝ) ^ j) (σ.height - 1)
  have hm0 : (σ.height : ℝ) ≠ 0 := by exact_mod_cast (show σ.height ≠ 0 by omega)
  apply Subtype.ext
  change (1 - (σ.walkBias h : ℝ)) * 0 + (σ.walkBias h : ℝ) *
    ((1 - (σ.selector h : ℝ)) * (innerBias t (σ.height - 2) : ℝ) +
      (σ.selector h : ℝ) * 1) = (σ.bias : ℝ)
  rw [σ.walkBias_coe h, σ.selector_coe h, σ.bias_from_next h]
  change _ = (t : ℝ) * ((σ.height : ℝ) - 1) / σ.height
  simp only [innerBias, show σ.height - 2 + 1 = σ.height - 1 by omega]
  have hcast : ((σ.height - 1 : ℕ) : ℝ) = (σ.height : ℝ) - 1 := by
    have hc : ((σ.height - 1 : ℕ) : ℝ) = (σ.height : ℝ) - ((1 : ℕ) : ℝ) :=
      Nat.cast_sub (show 1 ≤ σ.height by omega)
    simpa only [Nat.cast_one] using hc
  rw [hcast]
  dsimp only [t] at hS hSM hSp ⊢
  field_simp [hSM.ne', hSp.ne', hm0]
  rw [hS]
  ring

theorem expected_calls_bound (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.walkBias h : ℝ) * (1 - (σ.selector h : ℝ)) *
      calls (σ.next h).bias (σ.height - 2) ≤ 2 / 7 := by
  have hm : 0 < (scale σ.e σ.f : ℝ) := by exact_mod_cast σ.scale_pos h
  have hc := calls_nonneg (σ.next h).bias (σ.height - 2)
  rw [σ.selector_complement h]
  calc
    _ ≤ 1 * (1 / (scale σ.e σ.f : ℝ)) * calls (σ.next h).bias (σ.height - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (σ.walkBias h).2.2 (one_div_nonneg.mpr hm.le)) hc
    _ = (1 / (scale σ.e σ.f : ℝ)) * calls (σ.next h).bias (σ.height - 2) := by ring
    _ ≤ (1 / (scale σ.e σ.f : ℝ)) * (1 / (1 - ((σ.next h).bias : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (calls_le _ (σ.next_bias_lt_one h) _) (one_div_nonneg.mpr hm.le)
    _ ≤ _ := σ.offspring_bound h

end Parameters

/-- The normalized requested bias `(a/b)*p`, with margins used only to establish its domain. -/
def bias (p : unitInterval) (a b e f : ℤ) (h : Admissible p a b e f) : unitInterval :=
  (Parameters.mk a b e f h).bias

@[simp] theorem bias_coe (p : unitInterval) (a b e f : ℤ) (h : Admissible p a b e f) :
    (bias p a b e f h : ℝ) = (a : ℝ) * p / b := rfl

/-- Conditional credit in the contracting branch. -/
def contractingCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, F z ∂RealCoin.law p else F false

theorem contracting_expectation {p : unitInterval} (σ : Parameters p) (hab : σ.a ≤ σ.b)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ b, contractingCredit p F b ∂RealCoin.law
      (RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab) =
      RealCoin.credit σ.bias F := by
  let r := RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab
  have hbias : CoinConditional.bias p 0 r = σ.bias := by
    apply Subtype.ext
    change (1 - (r : ℝ)) * 0 + (r : ℝ) * p = (σ.a : ℝ) * p / σ.b
    dsimp [r, RationalCoin.bias]
    ring
  simpa only [contractingCredit, CoinConditional.firstCredit, CoinConditional.law,
    RealCoin.lintegral_law, RealCoin.credit_zero, hbias] using
    CoinConditional.expectation_preservation p 0 r F

def selectorCredit {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit (innerBias (σ.next h).bias (σ.height - 2)) F +
    ofReal (calls (σ.next h).bias (σ.height - 2)) * (2 * ε)

def walkCredit {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, selectorCredit σ h F ε z ∂RealCoin.law (σ.selector h) else F false

/-- The outer composition preserves linear credit; subcritical offspring finance amplification. -/
theorem expectation {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, walkCredit σ h F ε b ∂RealCoin.law (σ.walkBias h) ≤
      RealCoin.credit σ.bias F + ε := by
  have hinner := CoinConditional.credit_mixture 1
    (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h) F
  have houter := CoinConditional.credit_mixture
    (CoinConditional.bias 1 (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h))
    0 (σ.walkBias h) F
  simp only [RealCoin.credit_one] at hinner
  simp only [RealCoin.credit_zero] at houter
  rw [← hinner, σ.outer_bias h] at houter
  have hq := sub_nonneg.mpr (σ.selector h).2.2
  have hc := calls_nonneg (σ.next h).bias (σ.height - 2)
  have hcost : ofReal (σ.walkBias h : ℝ) * ofReal (1 - (σ.selector h : ℝ)) *
      ofReal (calls (σ.next h).bias (σ.height - 2)) * 2 ≤ 1 := by
    have hm := σ.expected_calls_bound h
    have hb := ENNReal.ofReal_le_ofReal (show
        (σ.walkBias h : ℝ) * (1 - (σ.selector h : ℝ)) *
          calls (σ.next h).bias (σ.height - 2) * 2 ≤ 1 by linarith)
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (σ.walkBias h).2.1 hq) hc),
      ENNReal.ofReal_mul (mul_nonneg (σ.walkBias h).2.1 hq),
      ENNReal.ofReal_mul (σ.walkBias h).2.1, ENNReal.ofReal_one] at hb
    norm_num at hb ⊢
    exact hb
  calc
    _ = RealCoin.credit (σ.walkBias h) (fun b => if b then
        RealCoin.credit (σ.selector h)
          (fun z => if z then F true else RealCoin.credit
            (innerBias (σ.next h).bias (σ.height - 2)) F)
        else F false) +
        (ofReal (σ.walkBias h : ℝ) * ofReal (1 - (σ.selector h : ℝ)) *
          ofReal (calls (σ.next h).bias (σ.height - 2)) * 2) * ε := by
      simp only [RealCoin.lintegral_law, walkCredit, selectorCredit, RealCoin.credit,
        RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
      ring
    _ ≤ _ := by
      rw [houter]
      exact add_le_add le_rfl (mul_le_of_le_one_left (show 0 ≤ ε from zero_le) hcost)

end

end SampLib.LinearFactory
