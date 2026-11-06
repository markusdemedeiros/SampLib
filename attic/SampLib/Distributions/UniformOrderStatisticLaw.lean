module

public import SampLib.Distributions.UniformOrderStatistic
public import SampLib.Distributions.IntegerBetaCDF
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

/-! # The binomial count behind a uniform order statistic

Threshold patterns are disjoint product boxes. Counting boxes of each cardinality
therefore gives the binomial tail, including both endpoints of the unit interval.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.UniformOrderStatistic

noncomputable section

/-- The coordinates at or below a threshold. -/
def below {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≤ t)

/-- A threshold pattern fixes one half-line in every coordinate. -/
theorem below_fiber {n : ℕ} (t : ℝ) (s : Finset (Fin n)) :
    below t ⁻¹' {s} = Set.pi Set.univ (fun i => if i ∈ s then Iic t else Ioi t) := by
  classical
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_pi, mem_univ, true_implies]
  constructor
  · intro h i
    have hi : i ∈ below t x ↔ i ∈ s := by rw [h]
    simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hs : i ∈ s
    · simpa only [ite_eq_left hs, mem_Iic] using hi.mpr hs
    · simpa only [ite_eq_right hs, mem_Ioi] using lt_of_not_ge (fun h => hs (hi.mp h))
  · intro h
    apply Finset.ext
    intro i
    have := h i
    by_cases hi : i ∈ s <;> simp_all [below]

theorem measurableSet_below_fiber {n : ℕ} (t : ℝ) (s : Finset (Fin n)) :
    MeasurableSet (below t ⁻¹' {s}) := by
  classical
  rw [below_fiber]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => by split_ifs <;> measurability)

@[fun_prop] theorem measurable_below {n : ℕ} (t : ℝ) : Measurable (below (n := n) t) :=
  measurable_to_countable' (measurableSet_below_fiber t)

theorem unitLaw_Iic (t : ℝ) (ht : t ∈ Icc 0 1) :
    DyadicPosterior.unitLaw (Iic t) = ENNReal.ofReal t := by
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans ht.2⟩
  rw [DyadicPosterior.unitLaw, restrict_Ico_eq_restrict_Icc,
    Measure.restrict_apply measurableSet_Iic, hset]
  simp

theorem unitLaw_Ioi (t : ℝ) (ht : t ∈ Icc 0 1) :
    DyadicPosterior.unitLaw (Ioi t) = ENNReal.ofReal (1 - t) := by
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), unitLaw_Iic t ht,
    measure_univ]
  simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 ht.1).symm

/-- Each pattern has its product Bernoulli mass. -/
theorem below_fiber_measure (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1)
    (s : Finset (Fin n)) :
    UniformVector.law (fun _ : Fin n => []) (below t ⁻¹' {s}) =
      ENNReal.ofReal t ^ s.card * ENNReal.ofReal (1 - t) ^ (n - s.card) := by
  classical
  rw [below_fiber, UniformVector.law, Measure.pi_pi]
  simp only [DyadicPosterior.law_nil, apply_ite, unitLaw_Iic t ht, unitLaw_Ioi t ht]
  have hcomp : (Finset.univ.filter (fun i : Fin n => i ∉ s)) = Finset.univ \ s := by
    ext i
    simp
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const, hcomp,
    Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, Fintype.card_fin]

/-- Counting the disjoint patterns of a fixed size gives the binomial mass. -/
theorem count_measure (n m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    UniformVector.law (fun _ : Fin n => []) {x | (below t x).card = m} =
      (n.choose m : ℝ≥0∞) * ENNReal.ofReal t ^ m * ENNReal.ofReal (1 - t) ^ (n - m) := by
  classical
  have hset : {x : Fin n → ℝ | (below t x).card = m} =
      below t ⁻¹' ((Finset.univ : Finset (Fin n)).powersetCard m : Set (Finset (Fin n))) := by
    ext x
    simp
  rw [hset, ← sum_measure_preimage_singleton _ (fun s _ => measurableSet_below_fiber t s)]
  trans ∑ _s ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ENNReal.ofReal t ^ m * ENNReal.ofReal (1 - t) ^ (n - m)
  · apply Finset.sum_congr rfl
    intro s hs
    rw [below_fiber_measure n t ht s, (Finset.mem_powersetCard.mp hs).2]
  · simp [mul_assoc]

/-- The CDF of the k-th coordinate is the corresponding binomial tail. -/
theorem rank_Iic (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (t : ℝ) (ht : t ∈ Icc 0 1) :
    (UniformVector.law (fun _ : Fin n => [])).map (rank n k hk) (Iic t) =
      ENNReal.ofReal (IntegerBetaCDF.tail n k t) := by
  classical
  have hcount : Measurable (fun x : Fin n → ℝ => (below t x).card) :=
    (measurable_of_finite Finset.card).comp (measurable_below t)
  have hset : rank n k hk ⁻¹' Iic t =
      (fun x : Fin n → ℝ => (below t x).card) ⁻¹' (Finset.Icc k n : Set ℕ) := by
    ext x
    simp only [mem_preimage, mem_Iic, Finset.mem_coe, Finset.mem_Icc, rank_le_iff, below]
    exact ⟨fun h => ⟨h, (Finset.card_filter_le _ _).trans (by simp)⟩, And.left⟩
  rw [Measure.map_apply (measurable_rank n k hk) measurableSet_Iic, hset,
    ← sum_measure_preimage_singleton _ (fun m _ => hcount (measurableSet_singleton m))]
  have hnonneg (m : ℕ) : 0 ≤ (n.choose m : ℝ) * t ^ m * (1 - t) ^ (n - m) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
      (pow_nonneg (sub_nonneg.mpr ht.2) _)
  rw [IntegerBetaCDF.tail, ENNReal.ofReal_sum_of_nonneg (fun m _ => hnonneg m)]
  apply Finset.sum_congr rfl
  intro m _
  change UniformVector.law (fun _ : Fin n => []) {x | (below t x).card = m} = _
  rw [count_measure n m t ht]
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _)),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_pow ht.1, ENNReal.ofReal_pow (sub_nonneg.mpr ht.2)]
  simp

/-- The canonical rank of independent uniforms has the beta order-statistic law. -/
theorem rank_law (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    (UniformVector.law (fun _ : Fin n => [])).map (rank n k hk) =
      ProbabilityTheory.betaMeasure (k : ℝ) ((n + 1 - k : ℕ) : ℝ) := by
  let μ := (UniformVector.law (fun _ : Fin n => [])).map (rank n k hk)
  let ν := ProbabilityTheory.betaMeasure (k : ℝ) ((n + 1 - k : ℕ) : ℝ)
  have : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure ((UniformVector.law (fun _ : Fin n => [])).map (rank n k hk)))
  have : IsProbabilityMeasure ν := ProbabilityTheory.isProbabilityMeasureBeta
    (by exact_mod_cast hk.1) (by exact_mod_cast (show 0 < n + 1 - k by omega))
  have hunit (t : ℝ) (ht : t ∈ Icc 0 1) : μ (Iic t) = ν (Iic t) := by
    exact (rank_Iic n k hk t ht).trans (IntegerBetaCDF.betaMeasure_Iic n k hk t ht).symm
  have hz : μ (Iic 0) = 0 := by
    change (UniformVector.law (fun _ : Fin n => [])).map (rank n k hk) (Iic 0) = 0
    rw [rank_Iic n k hk 0 (by norm_num), IntegerBetaCDF.tail_zero n k hk.1,
      ENNReal.ofReal_zero]
  have ho : μ (Iic 1) = 1 := by
    change (UniformVector.law (fun _ : Fin n => [])).map (rank n k hk) (Iic 1) = 1
    rw [rank_Iic n k hk 1 (by norm_num), IntegerBetaCDF.tail_one n k hk.2,
      ENNReal.ofReal_one]
  apply Measure.ext_of_Iic
  intro t
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ 1
    · exact hunit t ⟨h0, h1⟩
    · have h1t : Iic (1 : ℝ) ⊆ Iic t := Iic_subset_Iic.mpr (not_le.mp h1).le
      have hμ : μ (Iic t) = 1 := le_antisymm prob_le_one
        (ho ▸ measure_mono h1t)
      have hν : ν (Iic t) = 1 := le_antisymm prob_le_one
        ((hunit 1 (by norm_num) ▸ ho) ▸ measure_mono h1t)
      exact hμ.trans hν.symm
  · have ht0 : Iic t ⊆ Iic (0 : ℝ) := Iic_subset_Iic.mpr (not_le.mp h0).le
    have hμ : μ (Iic t) = 0 := le_zero_iff.mp (hz ▸ measure_mono ht0)
    have hν : ν (Iic t) = 0 := le_zero_iff.mp
      ((hunit 0 (by norm_num) ▸ hz) ▸ measure_mono ht0)
    exact hμ.trans hν.symm

end

end SampLib.UniformOrderStatistic
