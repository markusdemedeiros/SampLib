import SampLib.Latent.Laws.LatentCoin
import SampLib.Bernoulli.Laws.OneDivOnePlus

/-! # Latent reciprocal-coin credit

The reciprocal identity holds at each latent point, so it survives integration over the
posterior. A failed trial retries with doubled auxiliary credit.
-/

open scoped ENNReal

namespace SampLib.LatentReal.CoinReciprocal

noncomputable section

open MeasureTheory
open LatentCoin

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The reciprocal factory's bias at each latent point. -/
def bias (φ : Ω → unitInterval) (x : Ω) : unitInterval := OneDivOnePlus.bias (φ x)

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ) :
    Measurable (bias φ) := by
  unfold bias OneDivOnePlus.bias EvenParity.bias
  fun_prop

/-- A failed input trial retries with doubled auxiliary credit. -/
def inputCredit (φ : Ω → unitInterval) (G : Bool → Ω → ℝ≥0∞)
    (ε : ℝ≥0∞) (b : Bool) : Ω → ℝ≥0∞ :=
  if b then G false else fun x => kernel (bias φ) G x + 2 * ε

theorem measurable_inputCredit {φ : Ω → unitInterval} (hφ : Measurable φ)
    {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) (b : Bool) :
    Measurable (inputCredit φ G ε b) := by
  cases b
  · exact (measurable_kernel (measurable_bias hφ) hG).add measurable_const
  · exact hG false

/-- Credit for the outer fair selector. -/
def selectorCredit (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (G : Bool → Ω → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ x, G true x ∂D.posterior s
  else credit D s φ (inputCredit φ G ε)

theorem posterior_add_const (D : Model Ω S) (s : S) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) (ε : ℝ≥0∞) :
    (∫⁻ x, F x + ε ∂D.posterior s) = (∫⁻ x, F x ∂D.posterior s) + ε := by
  rw [lintegral_add_left hF _]
  simp

/-- Pointwise reciprocal conservation pays at most one auxiliary retry credit. -/
theorem expectation (D : Model Ω S) (s : S) (φ : Ω → unitInterval) (hφ : Measurable φ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (ε : ℝ≥0∞) :
    (∫⁻ b, selectorCredit D s φ G ε b ∂RealCoin.law VonNeumann.fairBias) ≤
      credit D s (bias φ) G + ε := by
  let K : Bool → Ω → ℝ≥0∞ := fun b x =>
    if b then G true x else kernel φ (inputCredit φ G ε) x
  have hK : ∀ b, Measurable (K b) := by
    intro b
    cases b
    · exact measurable_kernel hφ (measurable_inputCredit hφ hG ε)
    · exact hG true
  have hs : selectorCredit D s φ G ε = fun b => ∫⁻ x, K b x ∂D.posterior s := by
    funext b
    cases b <;> rfl
  have hp (x : Ω) : RealCoin.credit VonNeumann.fairBias (fun b => K b x) ≤
      kernel (bias φ) G x + ε := by
    simpa only [RealCoin.lintegral_law, OneDivOnePlus.fairCredit,
      OneDivOnePlus.coinCredit, kernel, inputCredit, ite_apply, bias, K] using
      OneDivOnePlus.expectation (φ x) (fun b => G b x) ε
  rw [RealCoin.lintegral_law, hs, ← credit_fixed_bias D s VonNeumann.fairBias K hK]
  calc
    _ ≤ ∫⁻ x, kernel (bias φ) G x + ε ∂D.posterior s := lintegral_mono hp
    _ = _ := posterior_add_const D s _ (measurable_kernel (measurable_bias hφ) hG) ε


end

end SampLib.LatentReal.CoinReciprocal
