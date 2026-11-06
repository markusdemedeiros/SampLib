import SampLib.Distributions.HanHoshiCell
import SampLib.Distributions.FiniteBoundaryBands

/-! # Finite-horizon credit for Han–Hoshi

A failed whole-cell test crosses a cumulative boundary. At depth `N`, pay one
extra credit only within one cell width of these finitely many boundaries.
The total extra mass vanishes, while an unresolved horizon costs at least one.
-/

open Set MeasureTheory Finset
open scoped ENNReal

namespace SampLib.HanHoshi

noncomputable section

def boundary (ws : List ℕ) (i : Fin ws.length) : ℝ := RealCategoricalCDF.upper ws i

def radius (N : ℕ) : ℝ := (2 ^ N : ℝ)⁻¹

def outputCredit (ws : List ℕ) (ht : 0 < ws.sum) (F : ℤ → ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  F (IncompleteInformation.quantile (RealCategoricalCDF.model ws ht) u)

def horizonCredit (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ) (F : ℤ → ℝ≥0∞) :
    ℝ → ℝ≥0∞ :=
  FiniteBoundaryBands.horizonCredit (boundary ws) (radius N) (outputCredit ws ht F)

theorem measurable_outputCredit (ws : List ℕ) (ht : 0 < ws.sum) (F : ℤ → ℝ≥0∞) :
    Measurable (outputCredit ws ht F) :=
  (measurable_of_countable F).comp (IncompleteInformation.measurable_quantile _)

theorem measurable_horizonCredit (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ)
    (F : ℤ → ℝ≥0∞) : Measurable (horizonCredit ws ht N F) :=
  FiniteBoundaryBands.measurable_horizonCredit _ _ _ (measurable_outputCredit ws ht F)

/-- Each accepted cell retains the complete, possibly infinite, output credit. -/
theorem return_credit (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ) (F : ℤ → ℝ≥0∞)
    (p : List Bool) (i : ℕ)
    (h : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 = some i) :
    F (i : ℤ) ≤ DyadicPosterior.credit p (horizonCredit ws ht N F) := by
  obtain ⟨hi, hfit⟩ := scan_some ws.sum _ _ ws 0 i h
  simp only [zero_add] at hfit
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [cell_resolves ws ht p i hi hfit] with u hu
  simp only [horizonCredit, FiniteBoundaryBands.horizonCredit, outputCredit, hu]
  exact le_self_add

/-- A cell crossing a boundary is contained in its one-cell-width error band. -/
theorem unresolved_mem (ws : List ℕ) (ht : 0 < ws.sum) (p : List Bool)
    (hnone : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 = none) :
    DyadicPosterior.cell p ⊆ FiniteBoundaryBands.bands (boundary ws) (radius p.length) := by
  obtain ⟨i, hi, hleft, hright⟩ := unresolved_boundary ws ht p hnone
  intro u hu
  rw [LatentUniform.cell_eq_rank] at hu
  apply mem_iUnion.mpr
  refine ⟨⟨i, hi⟩, ?_⟩
  change boundary ws ⟨i, hi⟩ - radius p.length < u ∧
    u < boundary ws ⟨i, hi⟩ + radius p.length
  have hwidth : ((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length -
      (UniformBag.rank p : ℝ) / 2 ^ p.length = radius p.length := by
    unfold radius
    field_simp
    ring
  dsimp only [boundary]
  constructor <;> linarith [hu.1, hu.2]

/-- Reaching the horizon unresolved would own at least one contradictory error credit. -/
theorem unresolved_credit (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ) (F : ℤ → ℝ≥0∞)
    (p : List Bool) (hlen : p.length = N)
    (hnone : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 = none) :
    1 ≤ DyadicPosterior.credit p (horizonCredit ws ht N F) := by
  subst N
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [DyadicPosterior.ae_mem_cell p] with u hu
  have hm := unresolved_mem ws ht p hnone hu
  simp only [horizonCredit, FiniteBoundaryBands.horizonCredit, Set.indicator_of_mem hm]
  exact le_add_self

/-- A finite horizon costs arbitrarily little beyond the desired categorical expectation. -/
theorem exists_horizon (ws : List ℕ) (ht : 0 < ws.sum) (F : ℤ → ℝ≥0∞)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, DyadicPosterior.credit [] (horizonCredit ws ht N F) ≤
      (∫⁻ i, F i ∂CategoricalCDF.law ws) + δ := by
  obtain ⟨N, hN⟩ := FiniteBoundaryBands.exists_horizon ws.length δ hδ
  refine ⟨N, ?_⟩
  have h := FiniteBoundaryBands.expectation_preservation (boundary ws) (radius N)
    (outputCredit ws ht F) (measurable_outputCredit ws ht F)
  change DyadicPosterior.credit [] (horizonCredit ws ht N F) ≤
    DyadicPosterior.credit [] (fun u =>
      F (IncompleteInformation.quantile (RealCategoricalCDF.model ws ht) u)) +
        (ws.length : ℝ≥0∞) * ENNReal.ofReal (2 * radius N) at h
  rw [RealCategoricalCDF.expectation ws ht F] at h
  exact h.trans (add_le_add le_rfl hN)

/-- One fresh fair bit splits the current posterior credit exactly. -/
theorem bit_expectation (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ) (F : ℤ → ℝ≥0∞)
    (p : List Bool) :
    (∑ b ∈ range 2, DyadicPosterior.credit (p ++ [decide (b = 1)])
      (horizonCredit ws ht N F)) / 2 = DyadicPosterior.credit p (horizonCredit ws ht N F) := by
  simpa only [sum_range_succ, sum_range_zero, zero_add, Nat.zero_ne_one, decide_false, decide_true]
    using (DyadicPosterior.credit_split p _ (measurable_horizonCredit ws ht N F)).symm

end

end SampLib.HanHoshi
