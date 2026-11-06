import SampLib.Common.FractionalPowerCore
import SampLib.Latent.LatentCoinSpec

/-! # Fractional-power credits over one shared latent probability

Conditioning on the same latent world gives the usual first-exit law. The
reciprocal hazard bounds survival uniformly, even where the input bias is zero.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.CoinFractionalPower

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (φ : Ω → unitInterval) (r : unitInterval) (x : Ω) : unitInterval :=
  FractionalPower.powerBias (φ x) r

def tail (φ : Ω → unitInterval) (r : unitInterval) (G : Bool → Ω → ℝ≥0∞)
    (n : ℕ) (x : Ω) : ℝ≥0∞ :=
  FractionalPower.tailCredit (φ x) r (fun b => G b x) n

def retryBound (r : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  FractionalPower.continueProb 0 r n

def inputCredit (φ : Ω → unitInterval) (r : unitInterval) (G : Bool → Ω → ℝ≥0∞)
    (n : ℕ) (c : ℝ≥0∞) (b : Bool) (x : Ω) : ℝ≥0∞ :=
  FractionalPower.inputCredit r n (fun bit => G bit x) (tail φ r G (n + 1) x + c) b

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ) (r : unitInterval) :
    Measurable (bias φ r) := by
  unfold bias FractionalPower.powerBias
  fun_prop

theorem measurable_continue {φ : Ω → unitInterval} (hφ : Measurable φ)
    (r : unitInterval) (n : ℕ) :
    Measurable (fun x => FractionalPower.continueProb (φ x) r n) := by
  unfold FractionalPower.continueProb
  fun_prop

theorem measurable_survival {φ : Ω → unitInterval} (hφ : Measurable φ)
    (r : unitInterval) (n depth : ℕ) :
    Measurable (fun x => AbsorbingChain.survival
      (FractionalPower.continueProb (φ x) r) n depth) := by
  induction depth generalizing n with
  | zero => exact measurable_const
  | succ depth ih =>
    simp only [AbsorbingChain.survival_succ]
    exact (measurable_continue hφ r n).mul (ih (n + 1))

theorem measurable_exit {φ : Ω → unitInterval} (hφ : Measurable φ)
    (r : unitInterval) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    Measurable (fun x => FractionalPower.exitCredit (φ x) r (fun b => G b x) n) := by
  have ht := hG true
  have hf := hG false
  unfold FractionalPower.exitCredit
  fun_prop

theorem measurable_tail {φ : Ω → unitInterval} (hφ : Measurable φ)
    (r : unitInterval) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    Measurable (tail φ r G n) := by
  unfold tail FractionalPower.tailCredit
  apply Measurable.tsum
  intro depth
  exact (measurable_survival hφ r n depth).mul (measurable_exit hφ r hG (n + depth))

theorem measurable_inputCredit {φ : Ω → unitInterval} (hφ : Measurable φ)
    (r : unitInterval) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b))
    (n : ℕ) (c : ℝ≥0∞) (b : Bool) : Measurable (inputCredit φ r G n c b) := by
  cases b
  · have ht := measurable_tail hφ r hG (n + 1)
    have hf := hG false
    change Measurable (fun x => RealCoin.credit (FractionalPower.hazardBias r n)
      (FractionalPower.hazardCredit (fun b => G b x) (tail φ r G (n + 1) x + c)))
    unfold RealCoin.credit RealCoin.pmf FractionalPower.hazardCredit
    simp only [ite_true, Bool.false_eq_true, ite_false]
    fun_prop
  · exact hG true

omit [MeasurableSpace Ω] in
theorem continue_le_bound (φ : Ω → unitInterval) (r : unitInterval) (n : ℕ) (x : Ω) :
    FractionalPower.continueProb (φ x) r n ≤ retryBound r n := by
  have hp : ENNReal.ofReal (1 - (φ x : ℝ)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (sub_le_self _ (φ x).2.1)
  simpa [retryBound, FractionalPower.continueProb, mul_comm] using
    mul_le_mul_right hp (ENNReal.ofReal (1 - (r : ℝ) / (n + 1)))

omit [MeasurableSpace Ω] in
/-- Pointwise conservation, with only the uniform unresolved-horizon mass overfunded. -/
theorem pointwise_budget (φ : Ω → unitInterval) (r : unitInterval)
    (G : Bool → Ω → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (x : Ω) :
    LatentCoin.kernel φ (inputCredit φ r G n c) x ≤ tail φ r G n x + retryBound r n * c := by
  have h := FractionalPower.round_expectation (φ x) r n (fun b => G b x)
    (tail φ r G (n + 1) x + c)
  rw [RealCoin.lintegral_law] at h
  change RealCoin.credit (φ x) (fun b => inputCredit φ r G n c b x) ≤ _
  rw [show (fun b => inputCredit φ r G n c b x) =
    FractionalPower.inputCredit r n (fun b => G b x) (tail φ r G (n + 1) x + c) from rfl, h]
  calc
    _ = tail φ r G n x + FractionalPower.continueProb (φ x) r n * c := by
      have htail : tail φ r G n x =
          FractionalPower.exitCredit (φ x) r (fun b => G b x) n +
            FractionalPower.continueProb (φ x) r n * tail φ r G (n + 1) x :=
        FractionalPower.tailCredit_succ (φ x) r (fun b => G b x) n
      rw [htail, mul_add, add_assoc]
    _ ≤ _ := by
      simpa only [mul_comm] using
        add_le_add_right (mul_le_mul_right (continue_le_bound φ r n x) c)
          (tail φ r G n x)

/-- Posterior integration preserves every output/latent credit, including infinity. -/
theorem expectation_budget (D : Model Ω S) (s : S) {φ : Ω → unitInterval}
    (hφ : Measurable φ) (r : unitInterval) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (n : ℕ) (c : ℝ≥0∞) :
    LatentCoin.credit D s φ (inputCredit φ r G n c) ≤
      (∫⁻ x, tail φ r G n x ∂D.posterior s) + retryBound r n * c := by
  unfold LatentCoin.credit
  calc
    _ ≤ ∫⁻ x, tail φ r G n x + retryBound r n * c ∂D.posterior s :=
      lintegral_mono (pointwise_budget φ r G n c)
    _ = _ := by
      rw [lintegral_add_left (measurable_tail hφ r hG n)]
      simp

theorem initial_credit (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (r : unitInterval) (hr : 0 < (r : ℝ)) (G : Bool → Ω → ℝ≥0∞) :
    (∫⁻ x, tail φ r G 0 x ∂D.posterior s) = LatentCoin.credit D s (bias φ r) G := by
  apply lintegral_congr
  intro x
  exact FractionalPower.tailCredit_zero (φ x) r (Or.inr hr) (fun b => G b x)

theorem absorbs (r : unitInterval) (hr : 0 < (r : ℝ)) :
    Filter.Tendsto (AbsorbingChain.survival (retryBound r) 0) Filter.atTop (nhds 0) :=
  FractionalPower.absorbs 0 r (Or.inr hr)

end

end SampLib.LatentReal.CoinFractionalPower
