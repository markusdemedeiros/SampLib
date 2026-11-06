module

public import SampLib.Distributions.LatentReal.UniformVector
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! # Uniform order statistics on a shared finite vector

The k-th value is the minimum, over all k-coordinate subsets, of their maximum.
This lattice formula is continuous even at ties and exposes the threshold event
as a count of coordinates below the threshold.
-/

open MeasureTheory

namespace SampLib.UniformOrderStatistic

noncomputable section

/-- A total finite maximum; empty subsets are excluded when defining a rank. -/
def subsetMaximum {n : ℕ} (s : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  if hs : s.Nonempty then s.sup' hs x else 0

theorem continuous_subsetMaximum {n : ℕ} (s : Finset (Fin n)) :
    Continuous (subsetMaximum s) := by
  classical
  unfold subsetMaximum
  split_ifs with hs
  · exact Continuous.finset_sup'_apply hs (fun i _ => continuous_apply i)
  · exact continuous_const

theorem candidates_nonempty (n k : ℕ) (hk : k ≤ n) :
    ((Finset.univ : Finset (Fin n)).powersetCard k).Nonempty :=
  Finset.powersetCard_nonempty.mpr (by simpa using hk)

/-- The canonical k-th value, with multiplicity retained at ties. -/
def rank (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).powersetCard k).inf'
    (candidates_nonempty n k hk.2) (fun s => subsetMaximum s x)

theorem continuous_rank (n k : ℕ) (hk : 0 < k ∧ k ≤ n) : Continuous (rank n k hk) :=
  Continuous.finset_inf'_apply (candidates_nonempty n k hk.2)
    (fun s _ => continuous_subsetMaximum s)

@[fun_prop] theorem measurable_rank (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    Measurable (rank n k hk) := (continuous_rank n k hk).measurable

/-- A rank lies below a threshold exactly when enough coordinates do. -/
theorem rank_le_iff (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (x : Fin n → ℝ) (t : ℝ) :
    rank n k hk x ≤ t ↔ k ≤ (Finset.univ.filter (fun i => x i ≤ t)).card := by
  classical
  rw [rank, Finset.inf'_le_iff]
  constructor
  · rintro ⟨s, hs, hmax⟩
    have hcard := (Finset.mem_powersetCard.mp hs).2
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    rw [subsetMaximum, dite_eq_left hne, Finset.sup'_le_iff] at hmax
    rw [← hcard]
    exact Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmax i hi⟩)
  · intro hcount
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hcount
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    rw [subsetMaximum, dite_eq_left hne, Finset.sup'_le_iff]
    exact fun i hi => (Finset.mem_filter.mp (hs hi)).2

end

end SampLib.UniformOrderStatistic
