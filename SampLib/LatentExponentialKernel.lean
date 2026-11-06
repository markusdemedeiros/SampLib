import SampLib.LatentCoinSpec
import SampLib.Samplers.ExpMinusFactory

/-! # Joint credit kernels for the decreasing-uniform exponential factory

The fixed-bias exponential identity is applied at each latent point. Tonelli then
exchanges the independent uniform draw with the current posterior. No latent
value or continuation credit is replaced by its mean.
-/

open ProbLang MeasureTheory
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.LatentReal.CoinExponential

noncomputable section

open LatentCoin

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (φ : Ω → unitInterval) (z : Ω) : unitInterval := ExpMinusFactory.bias (φ z)

omit [MeasurableSpace Ω] in
theorem bias_coe (φ : Ω → unitInterval) (z : Ω) :
    (bias φ z : ℝ) = Real.exp (-(φ z : ℝ)) := by
  simp [bias, ExpMinusFactory.bias]

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ) :
    Measurable (bias φ) := by
  unfold bias ExpMinusFactory.bias ExponentialFactory.decay
  fun_prop

def tail (φ : Ω → unitInterval) (x : ℝ) (b : Bool) (G : Bool → Ω → ℝ≥0∞)
    (z : Ω) : ℝ≥0∞ := ExpMinusFactory.credit (φ z) x b (fun a => G a z)

theorem measurable_tail {φ : Ω → unitInterval} (hφ : Measurable φ) (x : ℝ) (b : Bool)
    {G : Bool → Ω → ℝ≥0∞} (hG : ∀ a, Measurable (G a)) : Measurable (tail φ x b G) := by
  have ht := hG b
  have hf := hG (!b)
  unfold tail ExpMinusFactory.credit RealCoin.credit RealCoin.pmf ExponentialFactory.decay
  simp only [ite_true, Bool.false_eq_true, ite_false]
  fun_prop

def inputCredit (φ : Ω → unitInterval) (y : ℝ) (b : Bool) (G : Bool → Ω → ℝ≥0∞)
    (c : ℝ≥0∞) (a : Bool) (z : Ω) : ℝ≥0∞ :=
  ExpMinusFactory.coinCredit (φ z) y b (fun a => G a z) c a

theorem measurable_inputCredit {φ : Ω → unitInterval} (hφ : Measurable φ) (y : ℝ)
    (b : Bool) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ a, Measurable (G a))
    (c : ℝ≥0∞) (a : Bool) : Measurable (inputCredit φ y b G c a) := by
  cases a
  · exact hG b
  · exact (measurable_tail hφ y (!b) hG).add measurable_const

/-- Credit for the next independent uniform, retaining the current joint posterior. -/
def uniformCredit (D : Model Ω S) (s : S) (φ : Ω → unitInterval) (x : ℝ) (b : Bool)
    (G : Bool → Ω → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ExpMinusFactory.kernel (φ z) x b (fun a => G a z) c y ∂D.posterior s

private theorem measurable_joint {φ : Ω → unitInterval} (hφ : Measurable φ) (x : ℝ)
    (b : Bool) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ a, Measurable (G a)) (c : ℝ≥0∞) :
    Measurable (fun yz : ℝ × Ω =>
      ExpMinusFactory.kernel (φ yz.2) x b (fun a => G a yz.2) c yz.1) := by
  have ht : Measurable (fun yz : ℝ × Ω => G b yz.2) := (hG b).comp measurable_snd
  have hf : Measurable (fun yz : ℝ × Ω => G (!b) yz.2) :=
    (hG (!b)).comp measurable_snd
  have hp : Measurable (fun yz : ℝ × Ω => φ yz.2) := hφ.comp measurable_snd
  unfold ExpMinusFactory.kernel ExpMinusFactory.coinCredit ExpMinusFactory.credit
    RealCoin.credit RealCoin.pmf ExponentialFactory.decay
  simp only [ite_true, Bool.false_eq_true, ite_false, Bool.not_not]
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_const)
  · fun_prop
  · exact ht

theorem measurable_uniformCredit (D : Model Ω S) (s : S)
    {φ : Ω → unitInterval} (hφ : Measurable φ) (x : ℝ) (b : Bool)
    {G : Bool → Ω → ℝ≥0∞} (hG : ∀ a, Measurable (G a)) (c : ℝ≥0∞) :
    Measurable (uniformCredit D s φ x b G c) :=
  (measurable_joint hφ x b hG c).lintegral_prod_right

/-- Entering the callback uses the conditional input-coin protocol, with its joint credits. -/
theorem uniformCredit_below (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (x y : ℝ) (b : Bool) (G : Bool → Ω → ℝ≥0∞) (c : ℝ≥0∞) (hy : y < x) :
    uniformCredit D s φ x b G c y = credit D s φ (inputCredit φ y b G c) := by
  simp only [uniformCredit, ExpMinusFactory.kernel, ite_eq_left hy, credit, kernel, inputCredit]

theorem uniformCredit_exit (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (x y : ℝ) (b : Bool) (G : Bool → Ω → ℝ≥0∞) (c : ℝ≥0∞) (hy : ¬y < x) :
    uniformCredit D s φ x b G c y = ∫⁻ z, G b z ∂D.posterior s := by
  simp only [uniformCredit, ExpMinusFactory.kernel, ite_eq_right hy]

theorem posterior_add_const (D : Model Ω S) (s : S) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) (c : ℝ≥0∞) :
    (∫⁻ z, F z + c ∂D.posterior s) = (∫⁻ z, F z ∂D.posterior s) + c := by
  rw [lintegral_add_left hF]
  simp

/-- Tonelli lifts the pointwise exponential identity to arbitrary joint credits. -/
theorem expectation (D : Model Ω S) (s : S) {φ : Ω → unitInterval} (hφ : Measurable φ)
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (b : Bool) {G : Bool → Ω → ℝ≥0∞}
    (hG : ∀ a, Measurable (G a)) (c : ℝ≥0∞) :
    (∫⁻ y, uniformCredit D s φ x b G c y ∂unifUnit) =
      ∫⁻ z, tail φ x b G z + ENNReal.ofReal ((φ z : ℝ) * x) * c ∂D.posterior s := by
  unfold uniformCredit
  rw [lintegral_lintegral_swap (measurable_joint hφ x b hG c).aemeasurable]
  apply lintegral_congr
  intro z
  exact ExpMinusFactory.expectation (φ z) x hx b (fun a => G a z) c

/-- A fixed threshold cap gives a uniform termination factor for every latent input bias. -/
theorem budget (D : Model Ω S) (s : S) {φ : Ω → unitInterval} (hφ : Measurable φ)
    (B : unitInterval) (hB : 0 < (B : ℝ)) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (B : ℝ))
    (b : Bool) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ a, Measurable (G a)) (ε : ℝ≥0∞) :
    (∫⁻ y, uniformCredit D s φ x b G (ExponentialFactory.factor B * ε) y ∂unifUnit) ≤
      (∫⁻ z, tail φ x b G z ∂D.posterior s) + ε := by
  rw [expectation D s hφ x ⟨hx.1, hx.2.trans B.2.2⟩ b hG]
  calc
    _ ≤ ∫⁻ z, tail φ x b G z + ε ∂D.posterior s := by
      apply lintegral_mono
      intro z
      exact add_le_add le_rfl (ExponentialFactory.amplified_continuation (φ z) B hB x hx ε)
    _ = _ := posterior_add_const D s _ (measurable_tail hφ x b hG) ε

end

end SampLib.LatentReal.CoinExponential
