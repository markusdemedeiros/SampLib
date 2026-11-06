import SampLib.Weighted.Laws.RealCategoricalCDF

/-! # The cumulative interval of a categorical quantile -/

open Set

namespace SampLib.RealCategoricalCDF

noncomputable section

def lower (ws : List ℕ) (i : ℕ) : ℝ := ((ws.take i).sum : ℝ) / ws.sum

def upper (ws : List ℕ) (i : ℕ) : ℝ := ((ws.take (i + 1)).sum : ℝ) / ws.sum

@[simp] theorem prefix_nat (ws : List ℕ) (ht : 0 < ws.sum) (i : ℕ) :
    ((model ws ht).cdf (i : ℤ) : ℝ) = upper ws i := by
  simp [model, prefixProbability, upper]

@[simp] theorem prefix_pred (ws : List ℕ) (ht : 0 < ws.sum) (i : ℕ) :
    ((model ws ht).cdf ((i : ℤ) - 1) : ℝ) = lower ws i := by
  simp [model, prefixProbability, lower]

/-- The first strict CDF crossing lies in its unique half-open cumulative interval. -/
theorem quantile_interval (ws : List ℕ) (ht : 0 < ws.sum) (i : ℕ) (hi : i < ws.length)
    (u : ℝ) (hu : u ∈ Ico 0 1) :
    IncompleteInformation.quantile (model ws ht) u = (i : ℤ) ↔
      lower ws i ≤ u ∧ u < upper ws i := by
  let D := model ws ht
  let q := IncompleteInformation.quantile D u
  have hrange := (IncompleteInformation.quantile_range D u).1
  have hgrid : (i : ℤ) ∈ Icc 0 D.upper := by
    change (0 : ℤ) ≤ i ∧ (i : ℤ) ≤ (ws.length : ℤ) - 1
    omega
  have hright : q ≤ (i : ℤ) ↔ u < upper ws i := by
    simpa only [q, D, prefix_nat] using IncompleteInformation.quantile_le_iff D hu.2 i hgrid
  by_cases hz : i = 0
  · subst i
    have hlo : lower ws 0 = 0 := by simp [lower]
    rw [hlo]
    constructor
    · intro h
      exact ⟨hu.1, hright.mp h.le⟩
    · intro h
      exact le_antisymm (hright.mpr h.2) hrange
  · have hprev : (i : ℤ) - 1 ∈ Icc 0 D.upper := by
      change (0 : ℤ) ≤ (i : ℤ) - 1 ∧ (i : ℤ) - 1 ≤ (ws.length : ℤ) - 1
      omega
    have hleft : q ≤ (i : ℤ) - 1 ↔ u < lower ws i := by
      simpa only [q, D, prefix_pred] using
        IncompleteInformation.quantile_le_iff D hu.2 ((i : ℤ) - 1) hprev
    constructor
    · intro h
      have hn : ¬u < lower ws i := by
        intro hlo
        have hq := hleft.mpr hlo
        change q = (i : ℤ) at h
        omega
      exact ⟨not_lt.mp hn, hright.mp h.le⟩
    · intro h
      have hq := hright.mpr h.2
      have hn : ¬q ≤ (i : ℤ) - 1 := by
        intro hlo
        exact not_lt_of_ge h.1 (hleft.mp hlo)
      change q = (i : ℤ)
      omega

end

end SampLib.RealCategoricalCDF
