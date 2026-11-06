import SampLib.PSRN.Laws.FloorKernel
import SampLib.Latent.Laws.LatentBernoulli
import SampLib.PSRN.Support.LatentExponentialKernel
import SampLib.Bernoulli.ExpMinusRational

/-! # Splitting a conditional exponential trial at its integer part

The integer trial is fresh; the fractional trial retains the entire latent world.
Their pointwise product is `exp(-x)`, so arbitrary joint credits remain correlated.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.ExpMinusCoin

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The floor read resolves away from the grid, or from an exact first enclosure. -/
def Admissible (D : Model Ω S) (s : S) : Prop :=
  (∀ᵐ x ∂D.posterior s, 0 ≤ D.value x) ∧
    (Floor.AvoidsGrid D 1 s ∨ ∀ᵐ x ∂D.posterior s, D.error 1 x = 0)

theorem Admissible.refines {D : Model Ω S} {s t : S} (h : Admissible D s)
    (hst : D.refines s t) : Admissible D t :=
  ⟨(D.absolutelyContinuous hst).ae_le h.1,
    h.2.imp (fun hgrid => (D.absolutelyContinuous hst).ae_le hgrid)
      (fun hzero => (D.absolutelyContinuous hst).ae_le hzero)⟩

/-- A measurable extension of `exp(-x)` from the source's nonnegative domain. -/
def valueBias (x : ℝ) : unitInterval :=
  ⟨Real.exp (-max 0 x), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left _ _))⟩

@[fun_prop] theorem measurable_valueBias : Measurable valueBias := by
  unfold valueBias
  fun_prop

theorem valueBias_coe {x : ℝ} (hx : 0 ≤ x) :
    (valueBias x : ℝ) = Real.exp (-x) := by simp [valueBias, max_eq_right hx]

def bias (D : Model Ω S) (x : Ω) : unitInterval := valueBias (D.value x)

@[fun_prop] theorem measurable_bias (D : Model Ω S) : Measurable (bias D) :=
  measurable_valueBias.comp D.measurable_value

def fractionBias (D : Model Ω S) (z : ℤ) (x : Ω) : unitInterval :=
  LatentBernoulli.bias (D.value x - z)

theorem measurable_fractionBias (D : Model Ω S) (z : ℤ) : Measurable (fractionBias D z) :=
  LatentBernoulli.measurable_bias.comp (D.measurable_value.sub_const _)

def afterWhole (D : Model Ω S) (z : ℤ) (G : Bool → Ω → ℝ≥0∞)
    (b : Bool) (x : Ω) : ℝ≥0∞ :=
  if b then LatentCoin.kernel (CoinExponential.bias (fractionBias D z)) G x else G false x

theorem measurable_afterWhole (D : Model Ω S) (z : ℤ) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (b : Bool) : Measurable (afterWhole D z G b) := by
  cases b
  · change Measurable (G false)
    exact hG false
  · change Measurable (LatentCoin.kernel (CoinExponential.bias (fractionBias D z)) G)
    exact LatentCoin.measurable_kernel
      (CoinExponential.measurable_bias (measurable_fractionBias D z)) hG

def floorCredit (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞) (z : ℤ) (x : Ω) : ℝ≥0∞ :=
  RealCoin.credit (valueBias z) (fun b => afterWhole D z G b x)

theorem measurable_floorCredit (D : Model Ω S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (z : ℤ) : Measurable (floorCredit D G z) :=
  LatentCoin.measurable_kernel measurable_const (measurable_afterWhole D z G hG)

theorem whole_expectation (D : Model Ω S) (s : S) (z : ℤ) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    (∫⁻ x, floorCredit D G z x ∂D.posterior s) =
      ∫⁻ b, (∫⁻ x, afterWhole D z G b x ∂D.posterior s) ∂RealCoin.law (valueBias z) := by
  simpa only [RealCoin.lintegral_law, LatentCoin.credit, LatentCoin.kernel, floorCredit] using
    LatentCoin.credit_fixed_bias D s (valueBias z) (afterWhole D z G)
      (measurable_afterWhole D z G hG)

theorem whole_bias (z : ℤ) (hz : 0 ≤ z) :
    valueBias z = ExpMinusRational.bias z 1 hz (by norm_num) := by
  apply Subtype.ext
  have hzR : 0 ≤ (z : ℝ) := by exact_mod_cast hz
  simp [valueBias_coe hzR, ExpMinusRational.bias]

theorem whole_nonneg {D : Model Ω S} {s : S} {z : ℤ}
    (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x)
    (hfloor : ∀ᵐ x ∂D.posterior s, Floor.output D 1 x = z) : 0 ≤ z := by
  obtain ⟨x, hx, hz⟩ := (hnonneg.and hfloor).exists
  have hz' : ⌊D.value x⌋ = z := by simpa [Floor.output] using hz
  rw [← hz']
  exact Int.floor_nonneg.mpr hx

private theorem split_bias (x : ℝ) (hx : 0 ≤ x) :
    CoinConditional.bias
      (ExpMinusFactory.bias (LatentBernoulli.bias (x - ⌊x⌋)))
      0 (valueBias (⌊x⌋ : ℤ)) = valueBias x := by
  apply Subtype.ext
  have hz : 0 ≤ (⌊x⌋ : ℤ) := Int.floor_nonneg.mpr hx
  have hzR : 0 ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hz
  have hf : x - (⌊x⌋ : ℤ) ∈ Ico (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le x), by linarith [Int.lt_floor_add_one x]⟩
  simp only [CoinConditional.bias, Set.Icc.convexComb, Set.Icc.coe_zero,
    mul_zero, zero_add, ExpMinusFactory.bias,
    ExponentialFactory.decay_coe _ 1 zero_le_one, mul_one, LatentBernoulli.bias_coe hf,
    valueBias_coe hzR, valueBias_coe hx]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Splitting at the exact floor preserves every output-and-latent continuation. -/
theorem expectation (D : Model Ω S) (s : S) (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x)
    (G : Bool → Ω → ℝ≥0∞) :
    (∫⁻ x, Floor.outputCredit D 1 (floorCredit D G) x ∂D.posterior s) =
      LatentCoin.credit D s (bias D) G := by
  apply lintegral_congr_ae
  filter_upwards [hnonneg] with x hx
  have h := CoinConditional.expectation_preservation
    (CoinExponential.bias (fractionBias D ⌊D.value x⌋) x) 0
    (valueBias (⌊D.value x⌋ : ℤ)) (fun b => G b x)
  have hsplit : CoinConditional.bias
      (CoinExponential.bias (fractionBias D ⌊D.value x⌋) x) 0
      (valueBias (⌊D.value x⌋ : ℤ)) = bias D x := split_bias _ hx
  simpa [Floor.outputCredit, Floor.output, floorCredit, afterWhole,
    LatentCoin.kernel, CoinConditional.firstCredit, CoinConditional.law, hsplit,
    RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] using h

/-- The observed floor makes the fractional part a genuine unit-interval value. -/
theorem fraction_mem {D : Model Ω S} {s : S} {z : ℤ}
    (hfloor : ∀ᵐ x ∂D.posterior s, Floor.output D 1 x = z) :
    ∀ᵐ x ∂D.posterior s, D.value x - z ∈ Ico (0 : ℝ) 1 := by
  filter_upwards [hfloor] with x hx
  have hz : ⌊D.value x⌋ = z := by simpa [Floor.output] using hx
  rw [← hz]
  exact ⟨sub_nonneg.mpr (Int.floor_le _), by linarith [Int.lt_floor_add_one (D.value x)]⟩

end

end SampLib.LatentReal.ExpMinusCoin
