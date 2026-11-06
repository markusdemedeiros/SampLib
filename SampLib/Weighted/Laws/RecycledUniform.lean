import SampLib.Weighted.Laws.EntropyPoolKernel
import SampLib.Uniform.Laws.UniformInt

/-! # Accepted and rejected branches of entropy recycling

An accepted rectangle keeps its quotient. A rejected rank falls into the bounded residual
kernel.
-/

open scoped ENNReal

namespace SampLib.RecycledUniform

open MeasureTheory EntropyPool

noncomputable section

theorem cutoff_narrow (n width : ℕ) (hw : width < n) : cutoff n width = 0 := by
  simp [cutoff, Nat.div_eq_of_lt hw]

theorem residual_width (n width : ℕ) : width - cutoff n width = width % n := by
  have h := cutoff_add_mod n width
  omega

theorem accepted_wide (n width value : ℕ) (ha : value < cutoff n width) :
    n ≤ width := by
  by_contra hw
  rw [cutoff_narrow n width (Nat.lt_of_not_ge hw)] at ha
  exact Nat.not_lt_zero _ ha

theorem accepted_expectation (n value width : ℕ) (hn : 0 < n) (hv : value < width)
    (ha : value < cutoff n width) (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂recycledLaw n value width hn hv) = F (value % n, value / n, width / n) := by
  change (∫⁻ z, F z ∂recycledKernel n value width) = _
  rw [recycledKernel_expectation, ite_eq_left ha]

theorem rejected_expectation (n value width : ℕ) (hn : 0 < n) (hv : value < width)
    (ha : ¬value < cutoff n width) (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂recycledLaw n value width hn hv) =
      ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) (value - cutoff n width) := by
  change (∫⁻ z, F z ∂recycledKernel n value width) = _
  rw [recycledKernel_expectation, ite_eq_right ha]

theorem single_expectation (F : ℕ → ℝ≥0∞) : (∫⁻ r, F r ∂UniformInt.law 1) = F 0 := by
  simp [UniformInt.lintegral_law]

end

end SampLib.RecycledUniform
