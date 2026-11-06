import SampLib.Bernoulli.Laws.BernoulliRetry

/-! # Laws of the Portkey two-coin race

One trial passes the portkey gate, selects a side, and flips that side's input coin. This
module computes the exit and retry masses of a trial and proves that the trial conserves the
normalized output credit together with the amplified retry credit.
-/

open ENNReal (ofReal ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.TwoCoin

noncomputable section

/-- Success mass of a single trial. -/
def success (p r β : unitInterval) : ℝ := (β : ℝ) * r * p

/-- Failure mass includes the portkey's immediate exit. -/
def failure (q r β : unitInterval) : ℝ := 1 - (β : ℝ) + β * (1 - (r : ℝ)) * q

private theorem success_nonneg (p r β : unitInterval) : 0 ≤ success p r β :=
  mul_nonneg (mul_nonneg β.2.1 r.2.1) p.2.1

private theorem failure_nonneg (q r β : unitInterval) : 0 ≤ failure q r β :=
  add_nonneg (sub_nonneg.mpr β.2.2)
    (mul_nonneg (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2)) q.2.1)

/-- Accepted trials have the normalized Portkey success mass. -/
abbrev bias (p q r β : unitInterval) :=
  BernoulliRetry.bias (success p r β) (failure q r β)
    (success_nonneg p r β) (failure_nonneg q r β)

/-- Portkey success is the accepted first-side mass divided by the total exit mass. -/
theorem bias_coe (p q r β : unitInterval) :
    (bias p q r β : ℝ) = (β : ℝ) * r * p /
      (1 - (β : ℝ) + β * (r * (p : ℝ) + (1 - (r : ℝ)) * q)) := by
  change (β : ℝ) * r * p / ((β : ℝ) * r * p +
    (1 - (β : ℝ) + β * (1 - (r : ℝ)) * q)) = _
  congr 1
  ring

/-- Retry probability of one complete trial. -/
def retry (p q r β : unitInterval) : unitInterval :=
  ⟨(β : ℝ) * (r * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ))),
    mul_nonneg β.2.1 (add_nonneg (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))
      (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2))),
    by
      have h₁ := mul_nonneg r.2.1 p.2.1
      have h₂ := mul_nonneg (sub_nonneg.mpr r.2.2) q.2.1
      have hm : (r : ℝ) * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ)) ≤ 1 := by
        nlinarith
      calc
        _ ≤ (β : ℝ) * 1 := mul_le_mul_of_nonneg_left hm β.2.1
        _ ≤ 1 := by simpa using β.2.2⟩

@[simp] private theorem retry_coe (p q r β : unitInterval) :
    (retry p q r β : ℝ) = (β : ℝ) *
      (r * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ))) := rfl

private theorem trial_partition (p q r β : unitInterval) :
    success p r β + failure q r β + (retry p q r β : ℝ) = 1 := by
  dsimp [success, failure, retry]
  ring

/-- A trial with positive exit mass retries with probability below one. -/
theorem retry_lt_one (p q r β : unitInterval)
    (h : 0 < success p r β + failure q r β) : (retry p q r β : ℝ) < 1 := by
  linarith [trial_partition p q r β]

/-- Credit after an input coin; rejection pays the amplified retry credit. -/
def inputCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side accepted : Bool) : ℝ≥0∞ :=
  if accepted then F side else RealCoin.credit (bias p q r β) F +
    BernoulliRetry.factor (retry p q r β) * ε

/-- Credit after the selector chooses a side. -/
def choiceCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side : Bool) : ℝ≥0∞ :=
  if side then ∫⁻ b, inputCredit p q r β F ε true b ∂RealCoin.law p
  else ∫⁻ b, inputCredit p q r β F ε false b ∂RealCoin.law q

/-- Credit after the portkey gate. -/
def portkeyCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (proceed : Bool) : ℝ≥0∞ :=
  if proceed then ∫⁻ side, choiceCredit p q r β F ε side ∂RealCoin.law r else F false

/-- Partition one trial into its two exits and its retry event. -/
theorem expectation (p q r β : unitInterval) (h : 0 < success p r β + failure q r β)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, portkeyCredit p q r β F ε b ∂RealCoin.law β ≤
      RealCoin.credit (bias p q r β) F + ε := by
  have hf₁ := sub_nonneg.mpr β.2.2
  have hf₂ := mul_nonneg (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2)) q.2.1
  calc
    _ = ofReal (success p r β) * F true + ofReal (failure q r β) * F false +
        ofReal (retry p q r β : ℝ) *
          (RealCoin.credit (bias p q r β) F + BernoulliRetry.factor (retry p q r β) * ε) := by
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
        portkeyCredit, choiceCredit, inputCredit, ite_true, Bool.false_eq_true, ite_false]
      rw [show failure q r β = 1 - (β : ℝ) + β * (1 - (r : ℝ)) * q from rfl,
        ENNReal.ofReal_add hf₁ hf₂]
      simp only [success, retry_coe, ofReal_mul β.2.1, ofReal_mul r.2.1,
        ENNReal.ofReal_add (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))
          (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2)),
        ofReal_mul (sub_nonneg.mpr r.2.2),
        ofReal_mul (mul_nonneg β.2.1 r.2.1),
        ofReal_mul (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2))]
      ring
    _ ≤ _ := BernoulliRetry.expectation _ _ (success_nonneg p r β)
      (failure_nonneg q r β) (retry p q r β) (retry_lt_one p q r β h)
      (trial_partition p q r β) F ε

end

end SampLib.TwoCoin
