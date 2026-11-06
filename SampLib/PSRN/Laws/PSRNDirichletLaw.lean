module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! # Joint Dirichlet laws from normalized independent gamma variables

A single sum normalizes the whole vector. Shape-one coordinates give the
exponential construction of the uniform simplex law, including dimension one.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.PSRNDirichletLaw

noncomputable section

variable {n : ℕ}

/-- The common normalizer, retained jointly by all coordinates. -/
def total (x : Fin n → ℝ) : ℝ := ∑ i, x i

def normalize (x : Fin n → ℝ) (i : Fin n) : ℝ := x i / total x

@[fun_prop] theorem measurable_normalize : Measurable (normalize (n := n)) := by
  unfold normalize total
  fun_prop

/-- Independent unit-rate gamma variables before sharing their common normalizer. -/
def proposal (shape : Fin n → ℝ) (_hshape : ∀ i, 0 < shape i) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gammaMeasure (shape i) 1)

instance (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) :
    IsProbabilityMeasure (proposal shape hshape) := by
  have (i : Fin n) : IsProbabilityMeasure (gammaMeasure (shape i) 1) :=
    isProbabilityMeasure_gammaMeasure (hshape i) zero_lt_one
  unfold proposal
  infer_instance

/-- The canonical Dirichlet law with strictly positive shape parameters. -/
def law (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) : Measure (Fin n → ℝ) :=
  (proposal shape hshape).map normalize

instance (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) :
    IsProbabilityMeasure (law shape hshape) := by
  unfold law
  infer_instance

/-- Positive gamma shapes put no mass at zero or on the negative half-line. -/
theorem gamma_ae_pos (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  have : NullSingletonClass (gammaMeasure a r) := by unfold gammaMeasure; infer_instance
  have hz : gammaMeasure a r (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    simp [gammaPDF, gammaPDFReal, not_le.mpr hx]
  have hc : gammaMeasure a r (Iic 0) = 0 := by
    rw [← measure_congr (Iio_ae_eq_Iic (μ := gammaMeasure a r))]
    exact hz
  have ha : ∀ᵐ x ∂gammaMeasure a r, x ∉ Iic 0 := by
    have hs : {x : ℝ | ¬ x ∉ Iic (0 : ℝ)} = Iic 0 := by ext x; simp
    rw [ae_iff, hs]
    exact hc
  simpa only [mem_Iic, not_le] using ha

/-- All coordinates are positive together under the product law. -/
theorem ae_positive (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) :
    ∀ᵐ x ∂proposal shape hshape, ∀ i, 0 < x i := by
  have (i : Fin n) : IsProbabilityMeasure (gammaMeasure (shape i) 1) :=
    isProbabilityMeasure_gammaMeasure (hshape i) zero_lt_one
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun j => gammaMeasure (shape j) 1) i).quasiMeasurePreserving.ae
    (gamma_ae_pos (shape i) 1)

theorem total_pos (x : Fin n → ℝ) (hn : 0 < n) (hx : ∀ i, 0 < x i) : 0 < total x := by
  exact Finset.sum_pos (fun i _ => hx i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- Nonempty positive shapes give a strictly positive shared denominator almost surely. -/
theorem ae_total_pos (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) (hn : 0 < n) :
    ∀ᵐ x ∂proposal shape hshape, 0 < total x :=
  (ae_positive shape hshape).mono (fun x hx => total_pos x hn hx)

theorem normalize_pos (x : Fin n → ℝ) (hn : 0 < n) (hx : ∀ i, 0 < x i) (i : Fin n) :
    0 < normalize x i := div_pos (hx i) (total_pos x hn hx)

theorem sum_normalize (x : Fin n → ℝ) (hsum : total x ≠ 0) :
    ∑ i, normalize x i = 1 := by
  simp only [normalize, ← Finset.sum_div]
  exact div_self hsum

/-- Every normalized coordinate is positive and the shared sum is one almost surely. -/
theorem ae_simplex (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i) (hn : 0 < n) :
    ∀ᵐ y ∂law shape hshape, (∀ i, 0 < y i) ∧ (∑ i, y i) = 1 := by
  rw [law, ae_map_iff measurable_normalize.aemeasurable
    (by measurability : MeasurableSet {y : Fin n → ℝ | (∀ i, 0 < y i) ∧ (∑ i, y i) = 1})]
  filter_upwards [ae_positive shape hshape] with x hx
  exact ⟨normalize_pos x hn hx, sum_normalize x (total_pos x hn hx).ne'⟩

/-- In dimension one every positive shape produces the deterministic unit vector. -/
theorem law_singleton (shape : Fin 1 → ℝ) (hshape : ∀ i, 0 < shape i) :
    law shape hshape = Measure.dirac (fun _ : Fin 1 => (1 : ℝ)) := by
  rw [law]
  calc
    _ = (proposal shape hshape).map (fun _ => fun _ : Fin 1 => (1 : ℝ)) := by
      apply Measure.map_congr
      filter_upwards [ae_positive shape hshape] with x hx
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [normalize, total, Fin.sum_univ_one]
      exact div_self (hx 0).ne'
    _ = _ := by simp

/-- Arbitrary joint credits are assigned before the one common normalization. -/
theorem expectation_preservation (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂law shape hshape = ∫⁻ x, F (normalize x) ∂proposal shape hshape :=
  lintegral_map hF measurable_normalize

/-- Shape one is the exponential construction of the uniform simplex law. -/
def simplex (n : ℕ) : Measure (Fin n → ℝ) := law (fun _ => 1) (fun _ => zero_lt_one)

theorem simplex_eq_exponentials : simplex n =
    (Measure.pi (fun _ : Fin n => expMeasure 1)).map normalize := rfl

instance : IsProbabilityMeasure (simplex n) := by unfold simplex; infer_instance

end

end SampLib.PSRNDirichletLaw
