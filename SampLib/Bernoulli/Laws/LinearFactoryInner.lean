import SampLib.Bernoulli.Laws.Gambler
import SampLib.Bernoulli.Laws.CoinConditional
import SampLib.Bernoulli.Laws.BernoulliEndpoints

/-! # The inner loop of the adaptive linear factory

The finite inner loop has a geometric-sum success law, and each step pays for exactly one
recursive factory call.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal BigOperators

namespace SampLib.LinearFactory

noncomputable section

private abbrev S (t : unitInterval) (n : ℕ) : ℝ := FiniteGeometricWalk.total (t : ℝ) n

/-- Success bias of the high-power subroutine. -/
def powerBias (t : unitInterval) (n : ℕ) : unitInterval :=
  FiniteGeometricWalk.bias (t : ℝ) t.2.1 (n + 1) (Nat.succ_pos _) n

@[simp] theorem powerBias_coe (t : unitInterval) (n : ℕ) :
    (powerBias t n : ℝ) = (t : ℝ) ^ n / S t (n + 1) := by
  simp [powerBias, FiniteGeometricWalk.bias, FiniteGeometricWalk.tail]

@[simp] theorem powerBias_zero (t : unitInterval) : powerBias t 0 = 1 := by
  exact FiniteGeometricWalk.bias_zero _ _ _ _

private theorem inner_numerator_le (t : unitInterval) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (t : ℝ) ^ (n + 1) ≤ S t (n + 1) := by
  calc
    _ = ∑ j ∈ Finset.range (n + 1), (t : ℝ) ^ (n + 1) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
      pow_le_pow_of_le_one t.2.1 t.2.2 (Finset.mem_range.mp hj).le

/-- Inner-loop success probability at height `n + 2`. -/
def innerBias (t : unitInterval) (n : ℕ) : unitInterval :=
  ⟨((n + 1 : ℕ) : ℝ) * (t : ℝ) ^ (n + 1) / S t (n + 1),
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg t.2.1 _))
      (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos _)).le,
    (div_le_one (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos _))).mpr
      (inner_numerator_le t n)⟩

theorem innerBias_zero (t : unitInterval) : innerBias t 0 = t := by
  apply Subtype.ext
  simp [innerBias, FiniteGeometricWalk.total]

theorem innerBias_succ (t : unitInterval) (n : ℕ) :
    (innerBias t (n + 1) : ℝ) = (t : ℝ) *
      ((powerBias t (n + 1) : ℝ) + (1 - (powerBias t (n + 1) : ℝ)) * innerBias t n) := by
  have hS : S t (n + 2) = S t (n + 1) + (t : ℝ) ^ (n + 1) :=
    Finset.sum_range_succ _ _
  simp only [innerBias, powerBias_coe, Nat.cast_add, Nat.cast_one]
  field_simp [(FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos n)).ne',
    (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos (n + 1))).ne']
  simp only [Nat.add_assoc]
  rw [hS, pow_succ]
  ring

/-- Expected recursive calls made by the finite inner loop at height `n + 2`. -/
def calls (t : unitInterval) : ℕ → ℝ
  | 0 => 1
  | n + 1 => 1 + (t : ℝ) * (1 - (powerBias t (n + 1) : ℝ)) * calls t n

theorem calls_nonneg (t : unitInterval) (n : ℕ) : 0 ≤ calls t n := by
  induction n with
  | zero => norm_num [calls]
  | succ n ih =>
    exact add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg t.2.1 (sub_nonneg.mpr (powerBias t (n + 1)).2.2)) ih)

/-- Each additional call requires another success of the transformed input coin. -/
theorem calls_le (t : unitInterval) (ht : (t : ℝ) < 1) (n : ℕ) :
    calls t n ≤ 1 / (1 - (t : ℝ)) := by
  have hd : 0 < 1 - (t : ℝ) := sub_pos.mpr ht
  induction n with
  | zero =>
    simpa only [calls] using (one_le_div hd).mpr (by linarith [t.2.1])
  | succ n ih =>
    have hw : 0 ≤ (t : ℝ) * (1 - (powerBias t (n + 1) : ℝ)) :=
      mul_nonneg t.2.1 (sub_nonneg.mpr (powerBias t (n + 1)).2.2)
    calc
      _ ≤ 1 + ((t : ℝ) * (1 - (powerBias t (n + 1) : ℝ))) * (1 / (1 - (t : ℝ))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hw)
      _ ≤ 1 + (t : ℝ) * (1 / (1 - (t : ℝ))) := by
        gcongr
        exact mul_le_of_le_one_right t.2.1 (sub_le_self _ (powerBias t (n + 1)).2.1)
      _ = _ := by field_simp; ring

def retryCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if n = 0 then F false
  else RealCoin.credit (innerBias t (n - 1)) F + ofReal (calls t (n - 1)) * δ

def powerCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ)
    (b : Bool) : ℝ≥0∞ :=
  if b then F true else retryCredit t F δ n

def factoryCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ)
    (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, powerCredit t F δ n z ∂RealCoin.law (powerBias t n) else F false

/-- One finite-loop step preserves its geometric success law and pays exactly one factory call. -/
theorem inner_expectation (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ) :
    RealCoin.credit t (factoryCredit t F δ n) + δ =
      RealCoin.credit (innerBias t n) F + ofReal (calls t n) * δ := by
  cases n with
  | zero =>
    simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, factoryCredit, powerCredit,
      retryCredit, powerBias_zero, innerBias_zero, calls]
  | succ n =>
    have hbias : CoinConditional.bias
        (CoinConditional.bias 1 (innerBias t n) (powerBias t (n + 1))) 0 t =
        innerBias t (n + 1) := by
      apply Subtype.ext
      change (1 - (t : ℝ)) * 0 + (t : ℝ) *
        ((1 - (powerBias t (n + 1) : ℝ)) * innerBias t n +
          (powerBias t (n + 1) : ℝ) * 1) = _
      rw [innerBias_succ]
      ring
    have hinner := CoinConditional.credit_mixture 1 (innerBias t n) (powerBias t (n + 1)) F
    have houter := CoinConditional.credit_mixture
      (CoinConditional.bias 1 (innerBias t n) (powerBias t (n + 1))) 0 t F
    simp only [RealCoin.credit_one] at hinner
    simp only [RealCoin.credit_zero] at houter
    rw [← hinner, hbias] at houter
    have hq := sub_nonneg.mpr (powerBias t (n + 1)).2.2
    have hcalls : ofReal (t : ℝ) * ofReal (1 - (powerBias t (n + 1) : ℝ)) *
        ofReal (calls t n) + 1 = ofReal (calls t (n + 1)) := by
      rw [calls, ENNReal.ofReal_add zero_le_one
          (mul_nonneg (mul_nonneg t.2.1 hq) (calls_nonneg t n)),
        ENNReal.ofReal_mul (mul_nonneg t.2.1 hq), ENNReal.ofReal_mul t.2.1,
        ENNReal.ofReal_one]
      ring
    calc
      _ = RealCoin.credit t (fun b => if b then
          RealCoin.credit (powerBias t (n + 1))
            (fun z => if z then F true else RealCoin.credit (innerBias t n) F)
          else F false) +
          (ofReal (t : ℝ) * ofReal (1 - (powerBias t (n + 1) : ℝ)) *
            ofReal (calls t n) + 1) * δ := by
        simp only [factoryCredit, powerCredit, retryCredit, Nat.add_one_ne_zero,
          ite_false, Nat.add_sub_cancel, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
          ite_true, Bool.false_eq_true]
        ring
      _ = _ := by rw [houter, hcalls]

end

end SampLib.LinearFactory
