module

public import SampLib.Combinatorial.Laws.ReservoirWeights

@[expose] public section

/-! # The ordered law of Algorithm R

The closed-form law satisfies the one-step reservoir identity, so the finite scan from
the initial reservoir has the closed joint law.
-/

open MeasureTheory Measure
open scoped ENNReal NNReal Classical

namespace SampLib.ReservoirLaw

noncomputable section

/-- Split the uniform ticket average into replacement and rejection tickets. -/
theorem advance_sum {M : Type*} [AddCommMonoid M] {n k : ℕ} (hkn : k ≤ n)
    (s : Slots k) (G : Slots k → M) :
    ∑ j : Fin (n + 1), G (advance n s j) =
      (∑ j : Fin k, G (Function.update s j n)) + (n + 1 - k) • G s := by
  have hlen : k + (n + 1 - k) = n + 1 := by omega
  have h := Fin.sum_univ_add (a := k) (b := n + 1 - k)
    (fun j => G (advance n s (j.cast hlen)))
  rw [Fin.sum_congr' (fun j : Fin (n + 1) => G (advance n s j)) hlen] at h
  have hsmall (j : Fin k) :
      advance n s ((j.castAdd (n + 1 - k)).cast hlen) = Function.update s j n := by
    rw [advance_lt _ _ j.isLt]
    rfl
  have hlarge (j : Fin (n + 1 - k)) :
      advance n s ((j.natAdd k).cast hlen) = s := by
    apply advance_ge
    simp only [Fin.val_cast, Fin.val_natAdd]
    omega
  simpa only [hsmall, hlarge, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

/-- A replacement fiber is indexed by the previous value of its overwritten slot. -/
theorem update_fiber_sum {n k : ℕ} (j : Fin k) (t : Slots k) (hj : t j = n) :
    (∑ s ∈ states n k, if Function.update s j n = t then weight n k s else 0) =
      ∑ x ∈ Finset.range n, weight n k (Function.update t j x) := by
  have hrestore (s : Slots k) (h : Function.update s j n = t) :
      Function.update t j (s j) = s := by
    rw [← h, Function.update_idem, Function.update_eq_self]
  have heq (s : Slots k)
      (h : (if Function.update s j n = t then weight n k s else 0) ≠ 0) :
      Function.update s j n = t := by
    by_contra hn
    exact h (by simp [hn])
  refine Finset.sum_bij_ne_zero (fun s _ _ => s j) ?_ ?_ ?_ ?_
  · intro s hs _
    exact Finset.mem_range.mpr ((mem_states n k s).mp hs j)
  · intro s _ hs r _ hr hsr
    rw [← hrestore s (heq s hs), ← hrestore r (heq r hr), hsr]
  · intro x hx hweight
    refine ⟨Function.update t j x, ?_, ?_, by simp⟩
    · exact (mem_states _ _ _).mpr (admissible_of_weight_ne_zero hweight).1
    · have ht : Function.update (Function.update t j x) j n = t := by
        rw [Function.update_idem, ← hj, Function.update_eq_self]
      simpa [ht] using hweight
  · intro s _ hs
    rw [ite_eq_left (heq s hs), hrestore s (heq s hs)]

theorem replacement_weight_sum {n k : ℕ} (j : Fin k) (t : Slots k) :
    (∑ s ∈ states n k, if Function.update s j n = t then weight n k s else 0) =
      if t j = n then ∑ x ∈ Finset.range n, weight n k (Function.update t j x) else 0 := by
  by_cases hj : t j = n
  · simpa only [hj, ite_true] using update_fiber_sum j t hj
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro s _
    have hne : Function.update s j n ≠ t := by
      intro he
      exact hj (by simpa using (congrFun he j).symm)
    simp only [hne, ite_false]

theorem retain_weight_sum (n k : ℕ) (t : Slots k) :
    (∑ s ∈ states n k, if s = t then weight n k s else 0) = weight n k t := by
  by_cases ht : t ∈ states n k
  · simp [ht]
  · have ha : ¬ Admissible n k t := fun h => ht ((mem_states n k t).mpr h.1)
    simp [ht, weight, ha]

/-- Reindexing the replacement fibers turns the ticket average into the closed incoming mass. -/
theorem ticket_weight_sum {n k : ℕ} (hkn : k ≤ n) (t : Slots k) :
    (∑ s ∈ states n k, ∑ j : Fin (n + 1),
      if advance n s j = t then weight n k s else 0) / (n + 1 : ℕ) =
        weight (n + 1) k t := by
  have hsplit (s : Slots k) : (∑ j : Fin (n + 1),
      if advance n s j = t then weight n k s else 0) =
        (∑ j : Fin k, if Function.update s j n = t then weight n k s else 0) +
          (n + 1 - k) • (if s = t then weight n k s else 0) :=
    advance_sum hkn s (fun u => if u = t then weight n k s else 0)
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [replacement_weight_sum]
  rw [← Finset.smul_sum, retain_weight_sum]
  simpa only [nsmul_eq_mul, add_comm] using incoming_weight hkn t

theorem step_singleton {k : ℕ} (n : ℕ) (s t : Slots k) :
    step n s {t} =
      (∑ j : Fin (n + 1), if advance n s j = t then (1 : ℝ≥0∞) else 0) / (n + 1 : ℕ) := by
  rw [← lintegral_indicator_one (measurableSet_singleton t), step_expectation, finish_one]
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]

/-- Algorithm R preserves the independent closed-form ordered law. -/
theorem law_step {n k : ℕ} (hkn : k ≤ n) :
    law (n + 1) k = ∑ s ∈ states n k, pmf n k s • step n s := by
  apply Measure.ext_of_singleton
  intro t
  rw [law_singleton, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, step_singleton]
  simp_rw [← mul_div_assoc, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [← ENNReal.sum_div]
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (ticket_weight_sum hkn t)
  rw [ENNReal.coe_div (by positivity)] at h
  push_cast at h
  simpa only [apply_ite, ENNReal.coe_zero, ← pmf_eq_coe_weight, Nat.cast_add,
    Nat.cast_one] using h.symm

/-- The mathematical one-step identity accepts arbitrary, possibly infinite, credits. -/
theorem expectation_step {n k : ℕ} (hkn : k ≤ n) (F : Slots k → ℝ≥0∞) :
    ∫⁻ s, finish n 1 s F ∂law n k = ∫⁻ t, F t ∂law (n + 1) k := by
  rw [law_step hkn]
  simp only [law, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul, step_expectation]

/-- The finite scan from the deterministic initial reservoir has the closed joint law. -/
theorem finish_bridge {n k : ℕ} (hkn : k ≤ n) (F : Slots k → ℝ≥0∞) :
    finish k (n - k) (initial k) F = ∫⁻ t, F t ∂law n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  simp only [Nat.add_sub_cancel_left]
  clear hkn
  induction m generalizing F with
  | zero => simp
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by omega, finish_append k m 1,
      ih, expectation_step (Nat.le_add_right k m)]

instance (n k : ℕ) [Fact (k ≤ n)] : IsProbabilityMeasure (law n k) where
  measure_univ := by
    have h := finish_bridge (Fact.out : k ≤ n) (fun _ => 1)
    simpa using h.symm

/-- The singleton formula exposes the selected-subset and remaining-slot factorial factors. -/
theorem law_singleton_closed {n k : ℕ} (hkn : k ≤ n) (s : Slots k) :
    law n k {s} =
      if Admissible n k s then
        ((n.choose k : ℝ≥0∞) * (lateCount s).factorial)⁻¹ else 0 := by
  rw [law_singleton]
  unfold pmf coefficient
  split_ifs
  · have hc : (n.choose k : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hkn).ne'
    rw [ENNReal.coe_inv (mul_ne_zero hc (by positivity))]
    norm_cast
  · rfl

end

end SampLib.ReservoirLaw
