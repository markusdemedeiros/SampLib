module

public import SampLib.Continuous.Laws.Gaussian
public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Termination and parity credit of Karney's Gaussian acceptance coin

The extra stopping coin leaves enough mass to amplify the retry credit, even when the
initial decreasing threshold is one.
-/

open ProbLang TotalEris.Examples
open scoped ENNReal NNReal

namespace SampLib.GaussianSelector

noncomputable section

abbrev bias := γBkx

section mathematics

open MeasureTheory

def factor (k : ℕ) : ℝ≥0 :=
  ⟨(2 * (k : ℝ) + 2) / (2 * k + 1), by positivity⟩

theorem one_lt_factor (k : ℕ) : 1 < factor k := by
  change (1 : ℝ) < (2 * k + 2) / (2 * k + 1)
  apply (lt_div_iff₀ (by positivity)).mpr
  linarith

/-- The remaining stopping mass pays for the amplified recursive call. -/
theorem expectation (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (n : ℕ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (ε : ℝ≥0∞) :
    ∫⁻ z, SCreditAmp F k x n y (factor k * ε) z ∂LawfulProbLangℝ.unifUnit ≤
      SCreditV F k x y n + ε := by
  have hq : 0 ≤ BiiFailProb k x * y := mul_nonneg (biiFailProb_nonneg k hx.1) hy.1
  have hamp : ENNReal.ofReal (BiiFailProb k x * y) * factor k ≤ 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hq]
    apply ENNReal.ofReal_le_one.mpr
    change (2 * (k : ℝ) + x) / (2 * k + 2) * y *
      ((2 * k + 2) / (2 * k + 1)) ≤ 1
    have hd : (0 : ℝ) < 2 * k + 1 := by positivity
    have heq : (2 * (k : ℝ) + x) / (2 * k + 2) * y *
        ((2 * k + 2) / (2 * k + 1)) = ((2 * k + x) * y) / (2 * k + 1) := by
      field_simp
    rw [heq, div_le_one hd]
    nlinarith [mul_nonneg (add_nonneg (by positivity) hx.1) (sub_nonneg.mpr hy.2)]
  rw [sCreditAmp_lintegral_eq F k x n y _ hx.1 hx.2 hy.1 hy.2]
  apply add_le_add le_rfl
  simpa only [mul_assoc] using (mul_le_of_le_one_left' hamp (a := ε))

theorem credit_eq (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    BCreditV F k x = RealCoin.credit (bias k x) F := by
  rw [← γBkx_credit_eq F k x hx]
  simp [RealCoin.credit, RealCoin.pmf, ENNReal.one_sub_ofReal (bias k x).2.1]

end mathematics

end

end SampLib.GaussianSelector
