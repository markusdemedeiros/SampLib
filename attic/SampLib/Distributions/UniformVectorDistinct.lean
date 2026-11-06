module

public import SampLib.Latent.Laws.UniformVector
public import SampLib.Common.Laws.DyadicRefinement

@[expose] public section

/-! # Distinct coordinates remain distinct after finite reads

Every dyadic posterior is absolutely continuous with respect to a nonatomic
uniform law. Two different roots therefore compare in finite time almost surely,
even after arbitrary adaptive observations of their shared world.
-/

open MeasureTheory

namespace SampLib.UniformVector

noncomputable section

theorem posterior_singleton (p : List Bool) (a : ℝ) : DyadicPosterior.law p {a} = 0 := by
  apply DyadicPosterior.law_absolutelyContinuous_unit p
  rw [DyadicPosterior.unitLaw, Measure.restrict_apply (measurableSet_singleton a)]
  exact measure_mono_null Set.inter_subset_left (by simp)

theorem ae_coordinate_ne {n : ℕ} (prefixes : Fin n → List Bool) (i j : Fin n)
    (hij : i ≠ j) : ∀ᵐ x ∂law prefixes, x i ≠ x j := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hij.symm
    rw [law_eq_map_split prefixes i]
    rw [ae_map_iff (join i).measurable.aemeasurable (by measurability)]
    have hprod : ∀ᵐ z ∂(DyadicPosterior.law (prefixes i)).prod
        (law (fun j => prefixes (i.succAbove j))), z.1 ≠ z.2 r := by
      apply (ae_prod_iff_ae_ae (by measurability)).mpr
      exact Filter.Eventually.of_forall fun a => ae_coordinate _ r
        (by simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton'] using
          posterior_singleton (prefixes (i.succAbove r)) a)
    simpa [join] using hprod

end

end SampLib.UniformVector
