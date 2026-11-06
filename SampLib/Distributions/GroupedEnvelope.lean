import SampLib.Distributions.DyadicGroups
import SampLib.Distributions.KnuthYaoCredits

/-! # Categorical rejection through dyadic envelope groups

The groups partition all positions. Each proposed cell pays its true weight
and its unused envelope credit, so summing the rectangles recovers the desired
categorical credit and one natural-number rejection mass. Credits may be infinite.
-/

open Finset MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.GroupedEnvelope

noncomputable section

open DyadicGroups

def position (k r : ℕ) : ℕ := lower k - 1 + r

def mass (n : ℕ) (envelope : ℕ → ℕ) (k : ℕ) : ℕ := width n k * envelope k

def total (n : ℕ) (envelope : ℕ → ℕ) : ℕ := ∑ k ∈ range n.size, mass n envelope k

def weightTotal (n : ℕ) (weight : ℕ → ℕ) : ℕ := ∑ i ∈ range n, weight i

def spare (n : ℕ) (weight envelope : ℕ → ℕ) : ℕ :=
  ∑ k ∈ range n.size, ∑ r ∈ range (width n k), (envelope k - weight (position k r))

def Dominates (n : ℕ) (weight envelope : ℕ → ℕ) : Prop :=
  ∀ k < n.size, ∀ r < width n k, weight (position k r) ≤ envelope k

def numerator (n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) (k : ℕ) :
    ℝ≥0∞ :=
  ∑ r ∈ range (width n k),
    ((weight (position k r) : ℝ≥0∞) * F (position k r) +
      ((envelope k - weight (position k r) : ℕ) : ℝ≥0∞) * R)

/-- The two uniform choices and the acceptance coin form one rectangular envelope. -/
def groupCredit (n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) (k : ℕ) :
    ℝ≥0∞ := numerator n weight envelope F R k / mass n envelope k

def masses (n : ℕ) (envelope : ℕ → ℕ) : List ℕ :=
  List.ofFn (fun k : Fin n.size => mass n envelope k)

@[simp] theorem masses_length (n : ℕ) (envelope : ℕ → ℕ) :
    (masses n envelope).length = n.size := by simp [masses]

theorem masses_sum (n : ℕ) (envelope : ℕ → ℕ) : (masses n envelope).sum = total n envelope := by
  rw [masses, List.sum_ofFn, Fin.sum_univ_eq_sum_range]
  rfl

/-- Each rectangle consists of the original weights and its unused integer tickets. -/
theorem mass_split (n : ℕ) (weight envelope : ℕ → ℕ) (hdom : Dominates n weight envelope)
    (k : ℕ) (hk : k < n.size) :
    (∑ r ∈ range (width n k), weight (position k r)) +
      (∑ r ∈ range (width n k), (envelope k - weight (position k r))) = mass n envelope k := by
  rw [← sum_add_distrib]
  calc
    _ = ∑ r ∈ range (width n k), envelope k :=
      sum_congr rfl (fun r hr => Nat.add_sub_of_le (hdom k hk r (mem_range.mp hr)))
    _ = _ := by simp [mass]

/-- No labelled mass is lost or counted twice when the dyadic rectangles are combined. -/
theorem total_split (n : ℕ) (weight envelope : ℕ → ℕ) (hdom : Dominates n weight envelope) :
    weightTotal n weight + spare n weight envelope = total n envelope := by
  unfold weightTotal spare total
  rw [← DyadicGroups.sum_groups n weight, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  exact mass_split n weight envelope hdom k (mem_range.mp hk)

theorem total_pos (n : ℕ) (weight envelope : ℕ → ℕ) (hdom : Dominates n weight envelope)
    (ht : 0 < weightTotal n weight) : 0 < total n envelope := by
  have := total_split n weight envelope hdom
  omega

private theorem zero_numerator (n : ℕ) (weight envelope : ℕ → ℕ)
    (hdom : Dominates n weight envelope) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞)
    (k : ℕ) (hk : k < n.size) (hmass : mass n envelope k = 0) :
    numerator n weight envelope F R k = 0 := by
  have he : envelope k = 0 :=
    (Nat.mul_eq_zero.mp hmass).resolve_left (width_pos n k).ne'
  unfold numerator
  apply sum_eq_zero
  intro r hr
  have hw : weight (position k r) = 0 := by
    have := hdom k hk r (mem_range.mp hr)
    omega
  simp only [hw, he, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]

/-- Zero-envelope groups contribute zero even with infinite continuation credits. -/
theorem mass_mul_credit (n : ℕ) (weight envelope : ℕ → ℕ)
    (hdom : Dominates n weight envelope) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞)
    (k : ℕ) (hk : k < n.size) :
    (mass n envelope k : ℝ≥0∞) * groupCredit n weight envelope F R k =
      numerator n weight envelope F R k := by
  by_cases hm : mass n envelope k = 0
  · rw [hm, Nat.cast_zero, zero_mul, zero_numerator n weight envelope hdom F R k hk hm]
  · exact ENNReal.mul_div_cancel (by exact_mod_cast hm) (by finiteness)

/-- Group summation preserves arbitrary labelled credits and all unused-envelope credit. -/
theorem sum_numerators (n : ℕ) (weight envelope : ℕ → ℕ) (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) :
    (∑ k ∈ range n.size, numerator n weight envelope F R k) =
      (∑ i ∈ range n, (weight i : ℝ≥0∞) * F i) + (spare n weight envelope : ℝ≥0∞) * R := by
  simp only [numerator, sum_add_distrib, position]
  rw [DyadicGroups.sum_groups n (fun i => (weight i : ℝ≥0∞) * F i)]
  congr 1
  simp only [spare, position, Nat.cast_sum, sum_mul]

/-- The canonical categorical choice of envelope groups has the expected rectangular credit. -/
theorem expectation (n : ℕ) (weight envelope : ℕ → ℕ) (hdom : Dominates n weight envelope)
    (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) :
    (∫⁻ k, groupCredit n weight envelope F R k ∂WeightedChoice.law (masses n envelope)) =
      ((∑ i ∈ range n, (weight i : ℝ≥0∞) * F i) +
        (spare n weight envelope : ℝ≥0∞) * R) / total n envelope := by
  rw [WeightedChoice.lintegral_law, masses, KnuthYaoColumns.weightedSum_ofFn,
    Fin.sum_univ_eq_sum_range (fun k =>
      (mass n envelope k : ℝ≥0∞) * groupCredit n weight envelope F R k)]
  change (∑ k ∈ range n.size, (mass n envelope k : ℝ≥0∞) * groupCredit n weight envelope F R k) /
      (masses n envelope).sum = _
  rw [masses_sum]
  congr 1
  calc
    _ = ∑ k ∈ range n.size, numerator n weight envelope F R k :=
      sum_congr rfl (fun k hk => mass_mul_credit n weight envelope hdom F R k (mem_range.mp hk))
    _ = _ := sum_numerators n weight envelope F R

/-- Any positive integer acceptance mass permits this finite retry amplification. -/
def factor (D : ℕ) : ℝ≥0 := 1 + (D : ℝ≥0)⁻¹

theorem one_lt_factor (D : ℕ) (hD : 0 < D) : 1 < factor D := by
  apply lt_add_of_pos_right
  exact inv_pos.mpr (by positivity)

/-- Accepted mass pays the target credit; unused rectangles fund strict retry amplification. -/
theorem expectation_preservation (n : ℕ) (weight envelope : ℕ → ℕ)
    (hdom : Dominates n weight envelope) (ht : 0 < weightTotal n weight)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    let C := (∑ i ∈ range n, (weight i : ℝ≥0∞) * F i) / weightTotal n weight
    (∫⁻ k, groupCredit n weight envelope F (C + factor (total n envelope) * ε) k
      ∂WeightedChoice.law (masses n envelope)) ≤ C + ε := by
  let T := weightTotal n weight
  let S := spare n weight envelope
  let D := total n envelope
  have hsplit : T + S = D := total_split n weight envelope hdom
  have hD : 0 < D := total_pos n weight envelope hdom ht
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by positivity
  have hDT : (D : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have hTT : (T : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by finiteness
  dsimp only
  let C := (∑ i ∈ range n, (weight i : ℝ≥0∞) * F i) / T
  have hC : (∑ i ∈ range n, (weight i : ℝ≥0∞) * F i) = T * C := by
    exact (ENNReal.mul_div_cancel hT0 hTT).symm
  have hparts : (T : ℝ≥0∞) / D + S / D = 1 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, hsplit, ENNReal.div_self hD0 hDT]
  have hamp : (S : ℝ≥0∞) / D * factor D ≤ 1 := by
    rw [ENNReal.coe_nnreal_eq]
    have hDR : (0 : ℝ) < D := by positivity
    have hb : (S : ℝ) * (1 + (D : ℝ)⁻¹) / D ≤ 1 := by
      have hsum : (T : ℝ) + S = D := by exact_mod_cast hsplit
      have hpos : (1 : ℝ) ≤ T := by exact_mod_cast ht
      rw [div_le_one hDR]
      field_simp
      nlinarith
    have he : (S : ℝ≥0∞) / D * ENNReal.ofReal (factor D : ℝ) =
        ENNReal.ofReal ((S : ℝ) * (1 + (D : ℝ)⁻¹) / D) := by
      rw [ENNReal.ofReal_div_of_pos hDR,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S)]
      simp only [ENNReal.ofReal_natCast]
      change _ = _ * ENNReal.ofReal (factor D : ℝ) / _
      simp only [ENNReal.div_eq_inv_mul]
      ring
    rw [he]
    exact ENNReal.ofReal_le_one.mpr hb
  rw [expectation n weight envelope hdom]
  nth_rw 1 [hC]
  change ((T : ℝ≥0∞) * C + S * (C + factor D * ε)) / D ≤ C + ε
  calc
    _ = ((T : ℝ≥0∞) / D + S / D) * C + (S / D * (factor D : ℝ≥0∞)) * ε := by
      simp only [ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hamp)

end

end SampLib.GroupedEnvelope
