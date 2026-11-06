import SampLib.Common.Laws.ListProduct
import SampLib.Uniform.Laws.RndIntExcRange

/-! # Stratified jitter law

The strata use rounded-down integer boundaries. Each stratum is nonempty when the number of
strata lies between one and the grid scale.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Stratified1D

noncomputable section

def boundary (scale strata i : ℕ) : ℕ := i * scale / strata

theorem boundary_lt (scale strata i : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    boundary scale strata i < boundary scale strata (i + 1) := by
  have hu : 1 ≤ scale / strata := (Nat.one_le_div_iff hs).2 h
  have hadd : i * scale / strata + scale / strata ≤ (i * scale + scale) / strata :=
    Nat.div_add_div_le_add_div
  dsimp [boundary]
  rw [Nat.add_mul, one_mul]
  omega

/-- Uniform jitter inside one of the rounded integer strata. -/
def coordinate (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) (i : ℕ) :
    Measure ℤ :=
  RndIntExcRange.law (boundary scale strata i) (boundary scale strata (i + 1))
    (Int.ofNat_lt.mpr (boundary_lt scale strata i hs h))

instance (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) (i : ℕ) :
    IsProbabilityMeasure (coordinate scale strata hs h i) := by
  unfold coordinate
  infer_instance

/-- One independent uniform point in each stratum, in stratum order. -/
def law (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) : Measure (List ℤ) :=
  ListProduct.law (coordinate scale strata hs h) 0 strata

instance (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    IsProbabilityMeasure (law scale strata hs h) := by unfold law; infer_instance

/-- Fubini gives the credit for a tail draw followed by its stratum's jitter. -/
theorem expectation (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale)
    (i n : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂coordinate scale strata hs h i
        ∂ListProduct.law (coordinate scale strata hs h) (i + 1) n =
      ∫⁻ ys, F ys ∂ListProduct.law (coordinate scale strata hs h) i (n + 1) :=
  ListProduct.expectation _ i n F

end

end SampLib.Stratified1D
