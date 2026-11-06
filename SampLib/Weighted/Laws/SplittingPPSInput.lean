module

public import SampLib.Weighted.Laws.SplittingPPSLaw
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! # Input populations and boundary cases for splitting PPS -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SplittingPPS

noncomputable section

/-- Input labels are their original positions, independently of probability sorting. -/
theorem tag_eq_mapIdx (ws : List ℕ) (count : ℕ) (label : ℤ) :
    tag count ws label = ws.mapIdx (fun i w => (count * w, label + i)) := by
  induction ws generalizing label with
  | nil => simp [tag]
  | cons w ws ih =>
    rw [tag, List.mapIdx_cons, ih (label + 1)]
    simp only [Nat.cast_zero, add_zero]
    congr 1
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro i hi
    apply Prod.ext
    · rfl
    · simp only [Nat.cast_add, Nat.cast_one]
      omega

theorem tag_labels (ws : List ℕ) (count : ℕ) (label : ℤ) :
    (tag count ws label).map Prod.snd =
      (List.range ws.length).map (fun (i : ℕ) => label + (i : ℤ)) := by
  rw [tag_eq_mapIdx]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_mapIdx, List.getElem_range]

/-- Sorting preserves the distinct original labels. -/
theorem prepare_labels_nodup (ws : List ℕ) (count : ℕ) (label : ℤ) :
    ((prepare count ws label).map Prod.snd).Nodup := by
  rw [((prepare_perm count ws label).map Prod.snd).nodup_iff, tag_labels]
  apply List.Nodup.map (fun i j h => by omega)
  exact List.nodup_range

/-- The initial numerator credit is the literal weighted sum over input positions. -/
theorem prepare_credit (ws : List ℕ) (count : ℕ) (G : ℤ → ℝ≥0∞) :
    numeratorCredit (prepare count ws 0) G =
      (ws.mapIdx (fun i w => ((count * w : ℕ) : ℝ≥0∞) * G (i : ℤ))).sum := by
  rw [numeratorCredit, ((prepare_perm count ws 0).map
    (fun a : Item => (a.1 : ℝ≥0∞) * G a.2)).sum_eq, tag_eq_mapIdx]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

private theorem all_at_capacity (items : List Item) (denominator : ℕ)
    (hb : ∀ a ∈ items, a.1 ≤ denominator)
    (hmass : (items.map Prod.fst).sum = items.length * denominator) :
    ∀ a ∈ items, a.1 = denominator := by
  induction items with
  | nil => simp
  | cons a items ih =>
    have htail : ∀ b ∈ items, b.1 ≤ denominator := fun b hb' => hb b (by simp [hb'])
    have hsum : (items.map Prod.fst).sum ≤ items.length * denominator := by
      have h := List.sum_le_length_nsmul (items.map Prod.fst) denominator
        (by simpa only [List.forall_mem_map] using htail)
      simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using h
    have ha := hb a (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at hmass
    have heq : a.1 = denominator := by omega
    have hmass' : (items.map Prod.fst).sum = items.length * denominator := by omega
    intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact heq
    · exact ih htail hmass' b hmem

/-- A full sample has inclusion probability one at every original label. -/
theorem full_credit {size : ℕ} (s : State size size) (G : ℤ → ℝ≥0∞) :
    numeratorCredit s.items G / s.denominator = ((s.items.map Prod.snd).map G).sum := by
  have hnum := all_at_capacity s.items s.denominator s.bounded
    (by simpa only [s.length_eq] using s.mass)
  have hcredit : numeratorCredit s.items G =
      (s.denominator : ℝ≥0∞) * (s.items.map (fun a => G a.2)).sum := by
    unfold numeratorCredit
    calc
      _ = (s.items.map (fun a => (s.denominator : ℝ≥0∞) * G a.2)).sum := by
        congr 1
        apply List.map_congr_left
        intro a ha
        rw [hnum a ha]
      _ = _ := List.sum_map_mul_left _ _ _
  rw [hcredit, ENNReal.div_eq_inv_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast s.positive.ne') (by finiteness), one_mul]
  simp only [List.map_map, Function.comp_def]

/-- The full input law includes empty and full selections as deterministic boundary cases. -/
def inputLaw (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (_hcount : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) : Measure (List ℤ) :=
  if hz : count = 0 then Measure.dirac [] else
    if hs : count < ws.length then
      law (Nat.pos_of_ne_zero hz) hs (State.initial ws count ht hcap)
    else Measure.dirac ((prepare count ws 0).map Prod.snd)

instance (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum) (hcount : count ≤ ws.length)
    (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    IsProbabilityMeasure (inputLaw ws count ht hcount hcap) := by
  unfold inputLaw
  split_ifs <;> infer_instance

end

end SampLib.SplittingPPS
