import SampLib.Weighted.Laws.EntropyPoolMass

/-! # Finite-leaf laws for an exact entropy pool

Once a pool needs a fresh bit, its width is below the requested bound. Every
subsequent acceptance therefore has quotient one and resets the pool to `(0,1)`.
The finite stopped laws retain each fixed rank's actual bias; only averaging all
ranks of a uniform pool gives a uniform output.
-/

open Finset MeasureTheory Filter
open scoped ENNReal Topology

namespace SampLib.EntropyPool

noncomputable section

/-- The finite-leaf output measure from one fixed bounded-width rank. -/
def boundedKernel (n width value : ℕ) : Measure ℕ :=
  ∑ r ∈ range n, (mass n width value r • Measure.dirac r)

/-- Valid bounded-width states absorb almost surely; the rank need not be uniform. -/
def boundedLaw (n width value : ℕ) (_hn : 0 < n) (_hw : width < n)
    (_hv : value < width) : Measure ℕ := boundedKernel n width value

instance (n width value : ℕ) (hn : 0 < n) (hw : width < n) (hv : value < width) :
    IsProbabilityMeasure (boundedLaw n width value hn hw hv) where
  measure_univ := by simpa [boundedLaw, boundedKernel] using sum_mass n width value hn hw hv

/-- The fixed-rank law accepts arbitrary, possibly infinite continuation credits. -/
theorem lintegral_boundedKernel (n width value : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ r, F r ∂boundedKernel n width value) =
      ∑ r ∈ range n, mass n width value r * F r := by
  simp [boundedKernel, lintegral_finsetSum_measure]

theorem boundedKernel_singleton (n width value r : ℕ) :
    boundedKernel n width value {r} = if r < n then mass n width value r else 0 := by
  simp [boundedKernel, Pi.single_apply, eq_comm]

/-- Averaging the fixed-state kernels exposes the uniform law, with no restriction on credits. -/
theorem ensemble_expectation (n width : ℕ) (hn : 0 < n) (hw : width < n)
    (F : ℕ → ℝ≥0∞) :
    (∑ v ∈ range width, ∫⁻ r, F r ∂boundedKernel n width v) =
      ((width : ℝ≥0∞) / n) * ∑ r ∈ range n, F r := by
  simp_rw [lintegral_boundedKernel]
  rw [sum_comm]
  calc
    _ = ∑ r ∈ range n, ((width : ℝ≥0∞) / n) * F r := by
      apply sum_congr rfl
      intro r hr
      rw [← sum_mul, uniform_mass n width r hn hw (mem_range.mp hr)]
    _ = _ := (mul_sum _ _ _).symm

/-- The actual initial pool has a uniform output law and no retained quotient. -/
theorem reset_expectation (n : ℕ) (hn : 0 < n) (hlarge : 1 < n) (F : ℕ → ℝ≥0∞) :
    (∫⁻ r, F r ∂boundedLaw n 1 0 hn hlarge (by decide)) =
      ∫⁻ r, F r ∂UniformInt.law n := by
  change (∫⁻ r, F r ∂boundedKernel n 1 0) = _
  rw [UniformInt.lintegral_law]
  simpa only [sum_range_one, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm, mul_one,
    one_mul] using
    ensemble_expectation n 1 hn hlarge F

/-- Expected eventual credit and the explicit geometric tail fund a finite source execution. -/
theorem horizon_lintegral_bound (n T width value : ℕ) (F : ℕ → ℝ≥0∞)
    (hn : 0 < n) (hw : width < n) (hv : value < width) :
    BitRecycler.credit .lower n F T width value ≤
      (∫⁻ r, F r ∂boundedLaw n width value hn hw hv) +
        ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  change _ ≤ (∫⁻ r, F r ∂boundedKernel n width value) + _
  rw [lintegral_boundedKernel]
  exact (horizon_bound n T width value F).trans
    (add_le_add le_rfl (tail_le n T width value hn hw hv))

end

end SampLib.EntropyPool
