module

public import SampLib.Distributions.SplittingPPSInput
public import Mathlib.Data.List.Indexes

@[expose] public section

/-! # Size and prescribed inclusion probabilities of the input law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SplittingPPS

noncomputable section

/-- Empty, interior, and full selections all have the requested size. -/
theorem input_length (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    ∀ᵐ xs ∂inputLaw ws count ht hc hcap, xs.length = count := by
  unfold inputLaw
  split_ifs with hz hs
  · subst count
    simp only [ae_dirac_eq, Filter.eventually_pure, List.length_nil]
  · exact ae_length _ _ _
  · simp only [ae_dirac_eq, Filter.eventually_pure, List.length_map, prepare_length]
    omega

/-- The law always samples distinct original positions. -/
theorem input_nodup (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    ∀ᵐ xs ∂inputLaw ws count ht hc hcap, xs.Nodup := by
  unfold inputLaw
  split_ifs with hz hs
  · simp only [ae_dirac_eq, Filter.eventually_pure, List.nodup_nil]
  · exact ae_nodup _ _ _ (prepare_labels_nodup ws count 0)
  · simpa only [ae_dirac_eq, Filter.eventually_pure] using prepare_labels_nodup ws count 0

/-- The expected sum of labelled credits is the prescribed PPS inclusion sum. -/
theorem input_inclusion_expectation (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) (G : ℤ → ℝ≥0∞) :
    ∫⁻ xs, (xs.map G).sum ∂inputLaw ws count ht hc hcap =
      (ws.mapIdx (fun i w => ((count * w : ℕ) : ℝ≥0∞) * G (i : ℤ))).sum / ws.sum := by
  rw [← prepare_credit ws count G]
  unfold inputLaw
  split_ifs with hz hs
  · subst count
    simp only [lintegral_dirac, List.map_nil, List.sum_nil, numeratorCredit,
      ((prepare_perm 0 ws 0).map (fun a : Item => (a.1 : ℝ≥0∞) * G a.2)).sum_eq]
    have hzero : ∀ a ∈ tag 0 ws 0, a.1 = 0 := by
      intro a ha
      have h := State.tag_bounded ws 0 0 0 (by simp) a ha
      omega
    have : ((tag 0 ws 0).map (fun a : Item => (a.1 : ℝ≥0∞) * G a.2)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      rw [hzero a ha, Nat.cast_zero, zero_mul]
    rw [this, ENNReal.zero_div]
  · exact inclusion_expectation _ _ _ G
  · have heq : count = ws.length := by omega
    subst count
    rw [lintegral_dirac]
    exact (full_credit (State.initial ws ws.length ht hcap) G).symm

/-- A position's inclusion probability is exactly `count * weight / total`. -/
theorem input_inclusion_probability (ws : List ℕ) (count i : ℕ) (hi : i < ws.length)
    (ht : 0 < ws.sum) (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    inputLaw ws count ht hc hcap {xs | (i : ℤ) ∈ xs} =
      ((count * ws[i] : ℕ) : ℝ≥0∞) / ws.sum := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet)]
  have heq : ∀ᵐ xs ∂inputLaw ws count ht hc hcap,
      Set.indicator {xs : List ℤ | (i : ℤ) ∈ xs} (1 : List ℤ → ℝ≥0∞) xs =
        (xs.map (fun j => if j = (i : ℤ) then (1 : ℝ≥0∞) else 0)).sum := by
    filter_upwards [input_nodup ws count ht hc hcap] with xs hxs
    rw [← List.sum_toFinset _ hxs]
    simp [Set.indicator_apply]
  rw [lintegral_congr_ae heq, input_inclusion_expectation, List.mapIdx_eq_ofFn, List.sum_ofFn]
  congr 1
  simp only [Int.natCast_inj, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin ws.length)]
  · simp
  · intro j _ hj
    have hji : j.val ≠ i := fun h => hj (Fin.ext h)
    simp only [hji, ite_false]
  · simp

end

end SampLib.SplittingPPS
