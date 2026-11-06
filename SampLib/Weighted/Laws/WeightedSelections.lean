import SampLib.Discrete.Laws.WeightedChoice
import SampLib.Common.Laws.WeightedPositiveSupport

/-! # Ordered sampling proportional to remaining weights

Each draw chooses a label proportionally to its current weight, then removes
that label's weight. The mathematical law stops when no positive weight remains.
For requests bounded by the positive-weight count, this is the Plackett–Luce law
on ordered distinct labels.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.WeightedSelections

noncomputable section

def positiveCount (ws : List ℕ) : ℕ := (ws.filter (0 < ·)).length

@[simp] theorem positiveCount_nil : positiveCount [] = 0 := rfl

@[simp] theorem positiveCount_cons (w : ℕ) (ws : List ℕ) :
    positiveCount (w :: ws) = (if 0 < w then 1 else 0) + positiveCount ws := by
  by_cases hw : 0 < w <;> simp [positiveCount, hw, Nat.add_comm]

theorem sum_pos (ws : List ℕ) (h : 0 < positiveCount ws) : 0 < ws.sum := by
  induction ws with
  | nil => simp at h
  | cons w ws ih =>
    by_cases hw : 0 < w
    · simp only [List.sum_cons]
      omega
    · have hw0 := Nat.eq_zero_of_not_pos hw
      have ht : 0 < positiveCount ws := by simpa [hw0] using h
      simpa [hw0] using ih ht

/-- A selected positive coordinate consumes exactly one available label. -/
theorem positiveCount_set (ws : List ℕ) (i : ℕ) (hi : 0 < ws[i]?.getD 0) :
    positiveCount (ws.set i 0) + 1 = positiveCount ws := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.getD_some] at hi
      simp [hi, Nat.add_comm]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have ht := ih i hi
      simp only [List.set_cons_succ, positiveCount_cons]
      omega

theorem index_lt (ws : List ℕ) (i : ℕ) (hi : 0 < ws[i]?.getD 0) : i < ws.length := by
  by_contra h
  simp [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hi

theorem positive_of_request (ws : List ℕ) (k : ℕ) (hk : k + 1 ≤ positiveCount ws) :
    0 < ws.sum := sum_pos ws (by omega)

theorem remaining_bound (ws : List ℕ) (i k : ℕ) (hi : 0 < ws[i]?.getD 0)
    (hk : k + 1 ≤ positiveCount ws) : k ≤ positiveCount (ws.set i 0) := by
  have := positiveCount_set ws i hi
  omega

def law (ws : List ℕ) : ℕ → Measure (List ℕ)
  | 0 => Measure.dirac []
  | k + 1 => if ws.sum = 0 then Measure.dirac [] else
      (WeightedChoice.law ws).bind (fun i => (law (ws.set i 0) k).map (List.cons i))

instance (ws : List ℕ) (k : ℕ) : IsProbabilityMeasure (law ws k) := by
  induction k generalizing ws with
  | zero => dsimp [law]; infer_instance
  | succ k ih =>
    by_cases hs : ws.sum = 0
    · simp only [law, ite_eq_left hs]
      infer_instance
    · let : NeZero ws.sum := ⟨hs⟩
      let (i : ℕ) := ih (ws.set i 0)
      simp only [law, ite_eq_right hs]
      constructor
      rw [Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
      have hm (i : ℕ) : (law (ws.set i 0) k).map (List.cons i) Set.univ = 1 := by
        rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
        simp
      simp_rw [hm]
      simp

/-- Conditional expectation after deleting the selected label's weight. -/
def continuation (ws : List ℕ) (k : ℕ) (F : List ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ is, F (i :: is) ∂law (ws.set i 0) k

@[simp] theorem expectation_zero (ws : List ℕ) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ is, F is ∂law ws 0 = F [] := by simp [law]

/-- The first proportional choice preserves the remaining ordered-selection expectation. -/
theorem expectation (ws : List ℕ) (hs : 0 < ws.sum) (k : ℕ)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ i, continuation ws k F i ∂WeightedChoice.law ws =
      ∫⁻ is, F is ∂law ws (k + 1) := by
  rw [law, ite_eq_right hs.ne', Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  congr 1
  funext i
  exact (lintegral_map (measurable_of_countable _) (measurable_of_countable _)).symm

/-- A nonempty request from a nonempty weighted population never returns nil. -/
theorem singleton_nil (ws : List ℕ) (hs : 0 < ws.sum) (k : ℕ) :
    law ws (k + 1) {[]} = 0 := by
  rw [law, ite_eq_right hs.ne', Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hempty (i : ℕ) : List.cons i ⁻¹' ({[]} : Set (List ℕ)) = ∅ := by
    ext is
    simp
  simp [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hempty]

/-- Each ordered likelihood factors into the current weight ratio and the residual likelihood. -/
theorem singleton_cons (ws : List ℕ) (hs : 0 < ws.sum) (k i : ℕ) (is : List ℕ) :
    law ws (k + 1) {i :: is} =
      ((ws[i]?.getD 0 : ℝ≥0∞) / ws.sum) * law (ws.set i 0) k {is} := by
  rw [law, ite_eq_right hs.ne', Measure.bind_apply (measurableSet_singleton _)
    (measurable_of_countable _).aemeasurable]
  have hkernel (j : ℕ) : (law (ws.set j 0) k).map (List.cons j) {i :: is} =
      ({i} : Set ℕ).indicator (fun _ => law (ws.set i 0) k {is}) j := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have hpre : List.cons j ⁻¹' ({i :: is} : Set (List ℕ)) =
        if j = i then {is} else ∅ := by
      ext xs
      by_cases h : j = i <;> simp [h]
    rw [hpre]
    by_cases h : j = i <;> simp [h]
  simp_rw [hkernel]
  rw [lintegral_indicator_const (measurableSet_singleton _), WeightedChoice.law_singleton]
  exact mul_comm _ _

/-- The Plackett–Luce product: one weight/remaining-total ratio per selected label. -/
def likelihood (ws : List ℕ) : List ℕ → ℝ≥0∞
  | [] => 1
  | i :: is => ((ws[i]?.getD 0 : ℝ≥0∞) / ws.sum) * likelihood (ws.set i 0) is

private theorem weight_le_sum (ws : List ℕ) (i : ℕ) : ws[i]?.getD 0 ≤ ws.sum := by
  induction ws generalizing i with
  | nil => simp
  | cons w ws ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem?_cons_succ, List.sum_cons]
      exact (ih i).trans (Nat.le_add_left _ _)

/-- Full-length singleton masses are precisely the successive ratio product. -/
theorem likelihood_eq (ws : List ℕ) (is : List ℕ) :
    law ws is.length {is} = likelihood ws is := by
  induction is generalizing ws with
  | nil => simp [law, likelihood]
  | cons i is ih =>
    by_cases hs : ws.sum = 0
    · have hw : ws[i]?.getD 0 = 0 := by have := weight_le_sum ws i; omega
      simp [law, hs, likelihood, hw]
    · rw [List.length_cons, singleton_cons ws (Nat.pos_of_ne_zero hs), ih]
      rfl

private theorem support_of_mass (ws : List ℕ) (k : ℕ) (hk : k ≤ positiveCount ws)
    (is : List ℕ) (hmass : law ws k {is} ≠ 0) :
    is.length = k ∧ is.Nodup ∧ ∀ i ∈ is, 0 < ws[i]?.getD 0 := by
  induction k generalizing ws is with
  | zero =>
    have hnil : is = [] := by
      by_contra h
      apply hmass
      simp [law, h]
    subst is
    simp
  | succ k ih =>
    have hs := positive_of_request ws k hk
    cases is with
    | nil => exact (hmass (singleton_nil ws hs k)).elim
    | cons i is =>
      rw [singleton_cons ws hs k i is] at hmass
      have hi : 0 < ws[i]?.getD 0 := by
        by_contra h
        apply hmass
        simp [Nat.eq_zero_of_not_pos h]
      have htail := ih (ws.set i 0) (remaining_bound ws i k hi hk) is
        (mul_ne_zero_iff.mp hmass).2
      have hnotmem : i ∉ is := by
        intro himem
        have hp := htail.2.2 i himem
        rw [List.getElem?_set_self (index_lt ws i hi)] at hp
        simp at hp
      refine ⟨by simp [htail.1], List.nodup_cons.mpr ⟨hnotmem, htail.2.1⟩, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · have hne : i ≠ j := by intro h; subst j; exact hnotmem hj
        simpa only [List.getElem?_set_ne hne] using htail.2.2 j hj

/-- Valid requests have their full length and contain distinct, originally positive labels. -/
theorem support (ws : List ℕ) (k : ℕ) (hk : k ≤ positiveCount ws) :
    ∀ᵐ is ∂law ws k, is.length = k ∧ is.Nodup ∧ ∀ i ∈ is, 0 < ws[i]?.getD 0 := by
  apply ae_iff_of_countable.mpr
  exact fun is hmass => support_of_mass ws k hk is hmass

/-- The normalized ordered-selection PMF, including zero mass off the requested length. -/
theorem law_singleton (ws : List ℕ) (k : ℕ) (hk : k ≤ positiveCount ws) (is : List ℕ) :
    law ws k {is} = if is.length = k then likelihood ws is else 0 := by
  by_cases h : is.length = k
  · rw [ite_eq_left h, ← h, likelihood_eq]
  · rw [ite_eq_right h]
    by_contra hmass
    exact h ((ae_iff_of_countable.mp (support ws k hk)) is hmass).1

end

end SampLib.WeightedSelections
