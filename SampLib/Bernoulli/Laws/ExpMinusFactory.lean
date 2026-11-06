import SampLib.Common.Laws.ExponentialFactory
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Bernoulli.Laws.CoinProduct

/-! # Laws of the decreasing-uniform factory for `exp (-p)`

At threshold `x`, the probability of reversing the current parity is
`∫₀ˣ p exp(-py) dy = 1-exp(-px)`. Once the first uniform is observed, all later
thresholds lie below a fixed cap strictly smaller than one, which pays for termination.
-/

open ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.ExpMinusFactory

noncomputable section

open ExponentialFactory

abbrev bias (p : unitInterval) := decay p 1

def relative (b : Bool) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then F (!b) else F b

def credit (p : unitInterval) (x : ℝ) (b : Bool) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (decay p x) (fun a => if a then F b else F (!b))

def coinCredit (p : unitInterval) (y : ℝ) (b : Bool) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then credit p y (!b) F + c else F b

def kernel (p : unitInterval) (x : ℝ) (b : Bool) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if y < x then RealCoin.credit p (coinCredit p y b F c) else F b

section mathematics

open MeasureTheory

theorem initial_credit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    credit p 1 true F = RealCoin.credit (bias p) F := by
  unfold credit
  congr 1
  funext a
  cases a <;> rfl

private theorem reversed_credit (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) :
    RealCoin.credit (unitInterval.symm (decay p x)) (relative b F) = credit p x b F := by
  simp only [RealCoin.credit, RealCoin.pmf, relative, credit, unitInterval.coe_symm_eq,
    Bool.false_eq_true, ite_true, ite_false, sub_sub_cancel]
  ring

private theorem nested_credit (p : unitInterval) (y : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit p (coinCredit p y b F c) =
      RealCoin.credit (p * decay p y) (relative b F) + ofReal (p : ℝ) * c := by
  have hbase : RealCoin.credit p (fun a => if a then credit p y (!b) F else F b) =
      RealCoin.credit (p * decay p y) (relative b F) := by
    have h := CoinProduct.expectation_preservation p (decay p y) (relative b F)
    simp only [CoinProduct.firstCredit, RealCoin.lintegral_law] at h
    have hflip : credit p y (!b) F = RealCoin.credit (decay p y) (relative b F) := by
      unfold credit
      congr 1
      funext a
      cases a <;> simp [relative]
    rw [hflip]
    simpa only [relative, Bool.false_eq_true, ite_false] using h
  rw [← hbase]
  simp only [RealCoin.credit, RealCoin.pmf, coinCredit,
    Bool.false_eq_true, ite_true, ite_false]
  ring

private theorem kernel_eq (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) :
    kernel p x b F c y = RealCoin.credit (flipBias p x y) (relative b F) +
      (if y < x then ofReal (p : ℝ) else 0) * c := by
  by_cases h : y < x
  · simp only [kernel, flipBias, ite_eq_left h, nested_credit]
  · simp [kernel, flipBias, h, RealCoin.credit, RealCoin.pmf, relative]

theorem measurable_kernel (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) : Measurable (kernel p x b F c) := by
  change Measurable (fun y => kernel p x b F c y)
  simp_rw [kernel_eq]
  exact (BernoulliMixture.measurable_credit _ (measurable_flipBias p x) _).add
    ((Measurable.ite measurableSet_Iio measurable_const measurable_const).mul_const c)

/-- Integrating the first-step flip mass preserves all parity credits. -/
theorem expectation (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ y, kernel p x b F c y ∂unifUnit = credit p x b F + ofReal ((p : ℝ) * x) * c := by
  simp_rw [kernel_eq]
  rw [lintegral_add_left (BernoulliMixture.measurable_credit _ (measurable_flipBias p x) _),
    BernoulliMixture.expectation unifUnit (flipBias p x) (measurable_flipBias p x)
      (unitInterval.symm (decay p x))
      (by simpa only [unitInterval.coe_symm_eq] using flip_mass p x hx) (relative b F),
    lintegral_mul_const _ (Measurable.ite measurableSet_Iio measurable_const measurable_const),
    continuation_mass p x hx, reversed_credit]

theorem budget (p B : unitInterval) (hB : 0 < (B : ℝ)) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (b : Bool) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ y, kernel p x b F (factor B * ε) y ∂unifUnit ≤ credit p x b F + ε := by
  rw [expectation p x ⟨hx.1, hx.2.trans B.2.2⟩ b F]
  exact add_le_add le_rfl (amplified_continuation p B hB x hx ε)

end mathematics

end

end SampLib.ExpMinusFactory
