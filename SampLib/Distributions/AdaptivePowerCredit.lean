import SampLib.Distributions.AdaptivePowerWalk

/-! # Credit preservation for the adaptive power walk

The power harmonicity pays output credit. The capped work budget pays a doubled
ambient credit on every recursive continuation, including probability amplification.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.AdaptivePowerWalk

noncomputable section

def drawBias (amplify : Bool) (t q : unitInterval) : unitInterval :=
  if amplify then q else FiniteGeometricWalk.down t t.2.1

def stepCredit (amplify : Bool) (ε : ℝ) (t t' : unitInterval) (n : ℕ)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if amplify then
    if b then IterateCoin.credit t' n F + ofReal (budget (ε / 2) n) * δ + 2 * δ
    else F false
  else
    let next := if b then n - 1 else n + 1
    IterateCoin.credit t next F + ofReal (budget ε next) * δ + 2 * δ

/-- Both source branches preserve power credit and fund one amplified continuation. -/
theorem expectation (amplify : Bool) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t t' q : unitInterval) (hmargin : (t : ℝ) ≤ 1 - ε) (n : ℕ) (hn : 0 < n)
    (hamplified : (t' : ℝ) = (t : ℝ) * amplification ε)
    (hselector : (q : ℝ) = selection ε n)
    (hthreshold : if amplify then 355 / 100 < (n : ℝ) * ε
      else (n : ℝ) * ε ≤ 355 / 100)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) :
    (∫⁻ b, stepCredit amplify ε t t' n F δ b ∂RealCoin.law (drawBias amplify t q)) ≤
      IterateCoin.credit t n F + ofReal (budget ε n) * δ + δ := by
  cases amplify
  · simp only [Bool.false_eq_true, ite_false] at hthreshold
    let r := FiniteGeometricWalk.down (t : ℝ) t.2.1
    have hcredit : (∫⁻ b, IterateCoin.credit t (if b then n - 1 else n + 1) F
        ∂RealCoin.law r) = IterateCoin.credit t n F := by
      calc
        _ = ∫⁻ b, CoinConditional.firstCredit (IterateCoin.bias t (n - 1))
            (IterateCoin.bias t (n + 1)) F b ∂RealCoin.law r := by
          apply lintegral_congr
          intro b
          cases b <;> simp [CoinConditional.firstCredit, IterateCoin.credit,
            RealCoin.lintegral_law]
        _ = _ := by
          rw [CoinConditional.expectation_preservation, CoinConditional.law, walk_bias t n hn,
            RealCoin.lintegral_law]
          rfl
    have hslack : ofReal (r : ℝ) * (ofReal (budget ε (n - 1)) + 2) +
        ofReal (1 - (r : ℝ)) * (ofReal (budget ε (n + 1)) + 2) ≤
        ofReal (budget ε n) + 1 := by
      have hreal : (r : ℝ) * (budget ε (n - 1) + 2) +
          (1 - (r : ℝ)) * (budget ε (n + 1) + 2) ≤ budget ε n + 1 := by
        dsimp [r]
        have hq : 1 - (t : ℝ) / (1 + (t : ℝ)) = 1 / (1 + (t : ℝ)) :=
          FiniteGeometricWalk.one_sub_down t t.2.1
        rw [hq]
        have h := walk_budget_drift ε t hε hε1 t.2.1 hmargin n hn hthreshold
        have hs : (t : ℝ) / (1 + (t : ℝ)) + 1 / (1 + (t : ℝ)) = 1 := by
          have hd : 0 < 1 + (t : ℝ) := by linarith [t.2.1]
          rw [← add_div, add_comm (t : ℝ) 1, div_self hd.ne']
        nlinarith
      have h := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_add (mul_nonneg r.2.1 (by linarith [budget_nonneg ε (n - 1)]))
          (mul_nonneg (sub_nonneg.mpr r.2.2) (by linarith [budget_nonneg ε (n + 1)])),
        ENNReal.ofReal_mul r.2.1, ENNReal.ofReal_mul (sub_nonneg.mpr r.2.2),
        ENNReal.ofReal_add (budget_nonneg ε (n - 1)) (by norm_num),
        ENNReal.ofReal_add (budget_nonneg ε (n + 1)) (by norm_num),
        ENNReal.ofReal_add (budget_nonneg ε n) zero_le_one] at h
      norm_num at h ⊢
      exact h
    calc
      _ = (∫⁻ b, IterateCoin.credit t (if b then n - 1 else n + 1) F ∂RealCoin.law r) +
          (ofReal (r : ℝ) * (ofReal (budget ε (n - 1)) + 2) +
            ofReal (1 - (r : ℝ)) * (ofReal (budget ε (n + 1)) + 2)) * δ := by
        simp only [drawBias, stepCredit, RealCoin.lintegral_law, RealCoin.credit,
          RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
        ring
      _ ≤ IterateCoin.credit t n F + (ofReal (budget ε n) + 1) * δ := by
        rw [hcredit]
        exact add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul_right hslack δ)
      _ = _ := by ring
  · simp only [ite_true] at hthreshold
    have hmix : CoinConditional.bias (IterateCoin.bias t' n) 0 q = IterateCoin.bias t n := by
      apply Subtype.ext
      simp only [CoinConditional.bias, Set.Icc.convexComb, Set.Icc.coe_zero,
        IterateCoin.bias, mul_zero, zero_add, hamplified, hselector]
      exact amplification_preserves ε t hε1 n
    have hcredit : (∫⁻ b, (if b then IterateCoin.credit t' n F else F false)
        ∂RealCoin.law q) = IterateCoin.credit t n F := by
      have h := CoinConditional.expectation_preservation (IterateCoin.bias t' n) 0 q F
      simpa [CoinConditional.firstCredit, CoinConditional.law, hmix,
        RealCoin.lintegral_law, IterateCoin.credit, RealCoin.credit, RealCoin.pmf] using h
    have hslack : ofReal (q : ℝ) * (ofReal (budget (ε / 2) n) + 2) ≤
        ofReal (budget ε n) + 1 := by
      have hreal : (q : ℝ) * (budget (ε / 2) n + 2) ≤ budget ε n + 1 := by
        rw [hselector]
        exact amplification_budget_drift ε hε hε1 n hn hthreshold
      have h := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_mul q.2.1,
        ENNReal.ofReal_add (budget_nonneg (ε / 2) n) (by norm_num),
        ENNReal.ofReal_add (budget_nonneg ε n) zero_le_one] at h
      norm_num at h ⊢
      exact h
    calc
      _ = (∫⁻ b, (if b then IterateCoin.credit t' n F else F false) ∂RealCoin.law q) +
          (ofReal (q : ℝ) * (ofReal (budget (ε / 2) n) + 2)) * δ := by
        simp only [drawBias, stepCredit, RealCoin.lintegral_law, RealCoin.credit,
          RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
        ring
      _ ≤ IterateCoin.credit t n F + (ofReal (budget ε n) + 1) * δ := by
        rw [hcredit]
        exact add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul_right hslack δ)
      _ = _ := by ring

end

end SampLib.AdaptivePowerWalk
