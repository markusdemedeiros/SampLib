import SampLib.Samplers.CumulativeDraw
import SampLib.Samplers.WeightedChoice

/-! # Cumulative sums and categorical quantiles

The first prefix strictly beyond a rank is precisely its categorical weight
block. Thus prefix-CDF inversion and the canonical categorical law agree.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SampLib.CategoricalCDF

noncomputable section

private theorem take_sum_mono (ws : List ℕ) (a b : ℕ) (h : a ≤ b) :
    (ws.take a).sum ≤ (ws.take b).sum := by
  have htake : (ws.take b).take a = ws.take a := by
    rw [List.take_take, Nat.min_eq_left h]
  have hs := List.sum_take_add_sum_drop (ws.take b) a
  rw [htake] at hs
  omega

private theorem take_sum_le (ws : List ℕ) (a : ℕ) : (ws.take a).sum ≤ ws.sum := by
  have := List.sum_take_add_sum_drop ws a
  omega

def cdf (ws : List ℕ) (x : ℤ) : ℤ := ((ws.take (x + 1).toNat).sum : ℤ)

@[simp] theorem cdf_nat (ws : List ℕ) (i : ℕ) :
    cdf ws (i : ℤ) = ((ws.take (i + 1)).sum : ℤ) := by simp [cdf]

/-- Prefix sums are a finite CDF with total mass equal to the sum of the weights. -/
def model (ws : List ℕ) (hs : 0 < ws.sum) : FiniteCDF.Model where
  lower := 0
  upper := (ws.length : ℤ) - 1
  nonempty := by have := List.length_pos_of_sum_ne_zero ws hs.ne'; omega
  scale := ws.sum
  positive := hs
  cdf := cdf ws
  monotone := by
    intro x hx y hy hxy
    change ((ws.take (x + 1).toNat).sum : ℤ) ≤ (ws.take (y + 1).toNat).sum
    exact_mod_cast take_sum_mono ws (x + 1).toNat (y + 1).toNat
      (Int.toNat_le_toNat (by omega))
  bounded := by
    intro x hx
    change (0 : ℤ) ≤ (ws.take (x + 1).toNat).sum ∧
      ((ws.take (x + 1).toNat).sum : ℤ) ≤ ws.sum
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast take_sum_le ws (x + 1).toNat⟩
  upper_mass := by simp [cdf]

/-- Categorical block order is exactly the order of cumulative prefix sums. -/
theorem category_le_iff (ws : List ℕ) (k : ℕ) (hk : k < ws.sum) (i : ℕ) :
    WeightedChoice.category ws k ≤ i ↔ k < (ws.take (i + 1)).sum := by
  induction ws generalizing k i with
  | nil => simp at hk
  | cons w ws ih =>
    by_cases h : k < w
    · simp only [WeightedChoice.category, ite_eq_left h,
        List.take_succ_cons, List.sum_cons]
      exact iff_of_true (Nat.zero_le i) (by omega)
    · cases i with
      | zero => simp [WeightedChoice.category, h]
      | succ i =>
        have ht : k - w < ws.sum := by simp only [List.sum_cons] at hk; omega
        simp only [WeightedChoice.category, ite_eq_right h,
          Nat.add_le_add_iff_right, List.take_succ_cons, List.sum_cons]
        rw [ih (k - w) ht i]
        omega

private theorem category_lt (ws : List ℕ) (hs : 0 < ws.sum) (k : ℕ) (hk : k < ws.sum) :
    WeightedChoice.category ws k < ws.length := by
  have hlen := List.length_pos_of_sum_ne_zero ws hs.ne'
  have hlast : ws.length - 1 + 1 = ws.length := Nat.sub_add_cancel hlen
  have h := (category_le_iff ws k hk (ws.length - 1)).2 (by simpa [hlast] using hk)
  omega

/-- First-reaching prefix quantiles are the canonical categorical labels. -/
theorem quantile_category (ws : List ℕ) (hs : 0 < ws.sum) (k : ℕ) (hk : k < ws.sum) :
    FiniteCDF.quantile (model ws hs) ⟨k, hk⟩ = (WeightedChoice.category ws k : ℤ) := by
  let D := model ws hs
  let i : Fin D.scale := ⟨k, hk⟩
  have hcat := category_lt ws hs k hk
  have hgrid : (WeightedChoice.category ws k : ℤ) ∈ Icc D.lower D.upper := by
    change (0 : ℤ) ≤ _ ∧ _ ≤ (ws.length : ℤ) - 1
    exact ⟨by positivity, by omega⟩
  apply le_antisymm
  · apply (FiniteCDF.quantile_le_iff D i _ hgrid).2
    have hp := (category_le_iff ws k hk (WeightedChoice.category ws k)).1 le_rfl
    change (k : ℤ) + 1 ≤ cdf ws (WeightedChoice.category ws k : ℤ)
    rw [cdf_nat]
    exact_mod_cast hp
  · have hq := FiniteCDF.quantile_mem D i
    have hq0 : 0 ≤ FiniteCDF.quantile D i := hq.1.1
    have hmass := hq.2
    change (k : ℤ) + 1 ≤ cdf ws (FiniteCDF.quantile D i) at hmass
    rw [← Int.toNat_of_nonneg hq0, cdf_nat] at hmass
    have hnat : k < (ws.take ((FiniteCDF.quantile D i).toNat + 1)).sum := by
      exact_mod_cast hmass
    have hc := (category_le_iff ws k hk (FiniteCDF.quantile D i).toNat).2 hnat
    have hc' : (WeightedChoice.category ws k : ℤ) ≤ (FiniteCDF.quantile D i).toNat := by
      exact_mod_cast hc
    simpa only [Int.toNat_of_nonneg hq0] using hc'

/-- Cumulative inversion preserves exactly the canonical categorical expectation. -/
theorem expectation (ws : List ℕ) (hs : 0 < ws.sum) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F z ∂FiniteCDF.law (model ws hs) =
      ∫⁻ i, F (i : ℤ) ∂WeightedChoice.law ws := by
  rw [← FiniteCDF.expectation, WeightedChoice.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law]
  apply congrArg (fun C : ℝ≥0∞ => C / ws.sum)
  apply Finset.sum_congr rfl
  intro k hk
  rw [FiniteCDF.position_of_lt _ k (Finset.mem_range.mp hk),
    quantile_category ws hs k (Finset.mem_range.mp hk)]

/-- The canonical categorical law on integer-encoded labels. -/
def law (ws : List ℕ) : Measure ℤ :=
  (WeightedChoice.law ws).map (fun i : ℕ => (i : ℤ))

instance (ws : List ℕ) [NeZero ws.sum] : IsProbabilityMeasure (law ws) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Both constructions define the same measure on integer-encoded labels. -/
theorem law_eq (ws : List ℕ) (hs : 0 < ws.sum) :
    FiniteCDF.law (model ws hs) = law ws := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  exact expectation ws hs F

/-- The scan stores one cumulative prefix after each input weight. -/
def scan (ws : List ℕ) (running : ℕ) : List ℕ := (ws.scanl (· + ·) running).tail

@[simp] theorem scan_nil (running : ℕ) : scan [] running = [] := by simp [scan]

@[simp] theorem scan_cons (w : ℕ) (ws : List ℕ) (running : ℕ) :
    scan (w :: ws) running = (running + w) :: scan ws (running + w) := by
  cases ws <;> simp [scan]

@[simp] theorem length_scan (ws : List ℕ) (running : ℕ) :
    (scan ws running).length = ws.length := by simp [scan]

theorem getElem_scan (ws : List ℕ) (running i : ℕ) (hi : i < (scan ws running).length) :
    (scan ws running)[i] = running + (ws.take (i + 1)).sum := by
  simp only [scan, List.getElem_tail, List.getElem_scanl]
  rw [List.foldl_eq_apply_foldr (init := 0), ← List.sum_eq_foldr]

/-- The deterministic prefix scan is the literal cumulative array of its CDF. -/
theorem scan_eq_cumulative (ws : List ℕ) (hs : 0 < ws.sum) :
    (scan ws 0).map (fun n : ℕ => (n : ℤ)) =
      CumulativeDraw.cumulative (model ws hs) ws.length := by
  apply List.ext_getElem
  · simp [CumulativeDraw.cumulative]
  · intro i hi hj
    simp only [CumulativeDraw.cumulative, List.getElem_map, List.getElem_ofFn]
    rw [getElem_scan]
    simp only [Nat.zero_add]
    exact (cdf_nat ws i).symm

end

end SampLib.CategoricalCDF
