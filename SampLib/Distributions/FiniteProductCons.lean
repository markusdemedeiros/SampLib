module

public import SampLib.Distributions.FiniteProductPosterior
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Head-and-tail credits for a finite dependent product -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.FiniteProductPosterior

noncomputable section

@[fun_prop] theorem measurable_cons {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] :
    Measurable (fun p : α 0 × (∀ i : Fin n, α i.succ) => Fin.cons p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst :
      α 0 × (∀ i : Fin n, α i.succ) → α 0))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

/-- Head-and-tail assembly gives exactly the original finite product measure. -/
theorem pi_eq_map_cons {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.pi μ = ((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))).map
      (fun p => Fin.cons p.1 p.2) := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_cons (MeasurableSet.pi countable_univ (fun i _ => hs i))]
  have hpre : (fun p : α 0 × (∀ i : Fin n, α i.succ) => Fin.cons p.1 p.2) ⁻¹'
      Set.pi univ s = s 0 ×ˢ Set.pi univ (fun i : Fin n => s i.succ) := by
    ext p
    simp only [mem_preimage, mem_univ_pi, Fin.forall_fin_succ, Fin.cons_zero,
      Fin.cons_succ, mem_prod]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_succ]

/-- Tonelli in the list order used by a finite vector constructor. -/
theorem expectation_cons {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : (∀ j, α j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂Measure.pi μ =
      ∫⁻ x, (∫⁻ tail, F (Fin.cons x tail) ∂Measure.pi (fun i => μ i.succ)) ∂μ 0 := by
  rw [pi_eq_map_cons μ, lintegral_map hF measurable_cons]
  exact lintegral_prod _ (hF.comp measurable_cons).aemeasurable

/-- The other Tonelli order allows the tail constructor to frame the observed head. -/
theorem expectation_cons_right {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (F : (∀ j, α j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂Measure.pi μ =
      ∫⁻ tail, (∫⁻ x, F (Fin.cons x tail) ∂μ 0) ∂Measure.pi (fun i => μ i.succ) := by
  rw [expectation_cons μ F hF]
  exact lintegral_lintegral_swap (hF.comp measurable_cons).aemeasurable

end

end SampLib.FiniteProductPosterior
