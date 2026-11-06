import SampLib.PSRN.Support.PSRNSimplexModel

/-! # The shared exponential sum is nonzero throughout every posterior refinement -/

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal MeasureTheory

/-- Strict positivity is established jointly before any coordinate is normalized. -/
theorem initial_nonzero (n : ℕ) (hn : 0 < n) :
    RepresentedReciprocalView.Nonzero (denominator n) (initial n) := by
  have h := PSRNDirichletLaw.ae_total_pos (fun _ : Fin n => (1 : ℝ))
    (fun _ => zero_lt_one) hn
  rw [← proposal_law n] at h
  have hmeas : MeasurableSet {y : Fin n → ℝ | 0 < PSRNDirichletLaw.total y} := by
    unfold PSRNDirichletLaw.total
    apply measurableSet_lt measurable_const
    fun_prop
  have hbefore := (ae_map_iff (measurable_vectorValue (original n)).aemeasurable hmeas).mp h
  change ∀ᵐ x ∂(CoordinateSum.model (world n) (original n) (original_sameWorld n)).posterior
    (initial n), (CoordinateSum.model (world n) (original n) (original_sameWorld n)).value x ≠ 0
  rw [(CoordinateSum.sameWorld (world n) (original n) (original_sameWorld n)).posterior_eq]
  filter_upwards [hbefore] with x hx
  rw [CoordinateSum.value_eq]
  exact hx.ne'

/-- Reading any coordinate preserves positivity of the common sum by absolute continuity. -/
theorem nonzero_of_refines (n : ℕ) (hn : 0 < n) (s : State n)
    (hs : (world n).refines (initial n) s) :
    RepresentedReciprocalView.Nonzero (denominator n) s :=
  RepresentedReciprocalView.nonzero_refines (denominator n)
    ((CoordinateSum.sameWorld (world n) (original n) (original_sameWorld n)).refines_iff _ _
      |>.mpr hs)
    (initial_nonzero n hn)

end

end SampLib.PSRNSimplex
