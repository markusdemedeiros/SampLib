module

public import SampLib.Distributions.SplittingPPSState
public import SampLib.Distributions.SplittingPPSMarginals
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Metrology.ProbLang.Discrete

@[expose] public section

/-! # The joint law of Deville–Tillé splitting

Each step either returns the upper block or reduces the common denominator.
This finite mixture recursion specifies the complete joint law; the linear
inclusion-credit identity identifies all its prescribed marginals.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SplittingPPS

noncomputable section

/-- The integer split amounts account for the entire probability mass. -/
theorem branch_mass (amount denominator : ℕ) (hd : 0 < denominator)
    (ha : amount ≤ denominator) :
    (amount : ℝ≥0∞) / denominator + ((denominator - amount : ℕ) : ℝ≥0∞) / denominator =
      1 := by
  rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_of_le ha,
    ENNReal.div_self (by exact_mod_cast hd.ne') (by finiteness)]

/-- One accepting outcome and one normalized residual distribution. -/
def blend (amount denominator : ℕ) (hd : 0 < denominator) (ha : amount ≤ denominator)
    (selected : List ℤ) (residual : ProbabilityMeasure (List ℤ)) : ProbabilityMeasure (List ℤ) := by
  refine ⟨((amount : ℝ≥0∞) / denominator) • Measure.dirac selected +
    (((denominator - amount : ℕ) : ℝ≥0∞) / denominator) • (residual : Measure (List ℤ)), ⟨?_⟩⟩
  simpa only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using
    branch_mass amount denominator hd ha

/-- Rejection moves to a strictly smaller denominator, so the joint-law recursion is finite. -/
def probability {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) : ProbabilityMeasure (List ℤ) :=
  if hnext : s.amount < s.denominator then
    blend s.amount s.denominator s.positive (s.amount_bounds hc hs).2.1 s.topLabels
      (probability hc hs (s.next hc hs hnext))
  else ⟨Measure.dirac s.topLabels, inferInstance⟩
termination_by s.denominator

decreasing_by exact s.next_lt hc hs hnext

/-- The exact joint law on the ordered list of selected labels. -/
def law {size count : ℕ} (hc : 0 < count) (hs : count < size) (s : State size count) :
    Measure (List ℤ) := probability hc hs s

instance {size count : ℕ} (hc : 0 < count) (hs : count < size) (s : State size count) :
    IsProbabilityMeasure (law hc hs s) :=
  inferInstanceAs (IsProbabilityMeasure (probability hc hs s : Measure (List ℤ)))

theorem law_step {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (hnext : s.amount < s.denominator) :
    law hc hs s = ((s.amount : ℝ≥0∞) / s.denominator) • Measure.dirac s.topLabels +
      (((s.denominator - s.amount : ℕ) : ℝ≥0∞) / s.denominator) •
        law hc hs (s.next hc hs hnext) := by
  have hprob : probability hc hs s =
      blend s.amount s.denominator s.positive (s.amount_bounds hc hs).2.1 s.topLabels
        (probability hc hs (s.next hc hs hnext)) := by
    rw [probability]
    exact dite_eq_left hnext
  change (probability hc hs s : Measure (List ℤ)) = _
  rw [hprob]
  rfl

theorem law_done {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (hnext : ¬s.amount < s.denominator) :
    law hc hs s = Measure.dirac s.topLabels := by
  have hprob : probability hc hs s =
      (⟨Measure.dirac s.topLabels, inferInstance⟩ : ProbabilityMeasure (List ℤ)) := by
    rw [probability]
    exact dite_eq_right hnext
  change (probability hc hs s : Measure (List ℤ)) = _
  rw [hprob]
  rfl

/-- Splitting preserves arbitrary continuation credit through its finite mixture. -/
theorem expectation {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ xs, F xs ∂law hc hs s =
      if hnext : s.amount < s.denominator then
        (s.amount : ℝ≥0∞) / s.denominator * F s.topLabels +
          ((s.denominator - s.amount : ℕ) : ℝ≥0∞) / s.denominator *
            ∫⁻ xs, F xs ∂law hc hs (s.next hc hs hnext)
      else F s.topLabels := by
  by_cases hnext : s.amount < s.denominator
  · rw [dite_eq_left hnext, law_step hc hs s hnext]
    simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  · rw [dite_eq_right hnext, law_done hc hs s hnext, lintegral_dirac]

private theorem terminal_credit {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (hterminal : s.amount = s.denominator) (G : ℤ → ℝ≥0∞) :
    numeratorCredit s.items G / s.denominator = (s.topLabels.map G).sum := by
  have hzero : numeratorCredit (adjust s.amount (size - count) s.items) G = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have hn := s.adjusted_bounded hc hs a ha
    rw [hterminal, Nat.sub_self] at hn
    have hnum : a.1 = 0 := by omega
    rw [hnum, Nat.cast_zero, zero_mul]
  rw [numeratorCredit_split s.amount (size - count) s.items (s.amount_le_top hc hs) G,
    hzero, add_zero, hterminal]
  simp only [State.topLabels, List.map_map, Function.comp_def, ENNReal.div_eq_inv_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast s.positive.ne') (by finiteness),
    one_mul]

/-- Every labelled inclusion credit retains its prescribed numerator through all splits. -/
theorem inclusion_expectation {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (G : ℤ → ℝ≥0∞) :
    ∫⁻ xs, (xs.map G).sum ∂law hc hs s = numeratorCredit s.items G / s.denominator := by
  rw [expectation hc hs s]
  split_ifs with hnext
  · rw [inclusion_expectation hc hs (s.next hc hs hnext) G]
    simpa only [State.next, State.topLabels, List.map_map, Function.comp_def] using
      inclusion_credit_expectation s.amount (size - count) s.denominator s.items
        (s.amount_le_top hc hs) hnext G
  · have hterminal := Nat.le_antisymm (s.amount_bounds hc hs).2.1 (Nat.le_of_not_gt hnext)
    exact (terminal_credit hc hs s hterminal G).symm
termination_by s.denominator

decreasing_by exact s.next_lt hc hs hnext

/-- Every draw has exactly the requested sample size. -/
theorem ae_length {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) : ∀ᵐ xs ∂law hc hs s, xs.length = count := by
  by_cases hnext : s.amount < s.denominator
  · rw [law_step hc hs s hnext, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simpa only [ae_dirac_eq, Filter.eventually_pure] using s.topLabels_length hs.le
    · apply Measure.ae_smul_measure
      exact ae_length hc hs (s.next hc hs hnext)
  · rw [law_done hc hs s hnext]
    simpa only [ae_dirac_eq, Filter.eventually_pure] using s.topLabels_length hs.le
termination_by s.denominator

decreasing_by exact s.next_lt hc hs hnext

/-- Label uniqueness is preserved by upper-block selection and residual reordering. -/
theorem ae_nodup {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (hlabels : (s.items.map Prod.snd).Nodup) :
    ∀ᵐ xs ∂law hc hs s, xs.Nodup := by
  have htop : s.topLabels.Nodup := by
    simpa only [State.topLabels, List.map_drop, List.nodup_iff_pairwise_ne] using
      (hlabels.drop (i := size - count))
  by_cases hnext : s.amount < s.denominator
  · rw [law_step hc hs s hnext, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simpa only [ae_dirac_eq, Filter.eventually_pure] using htop
    · apply Measure.ae_smul_measure
      exact ae_nodup hc hs (s.next hc hs hnext) ((s.next_labels hc hs hnext).nodup_iff.mpr hlabels)
  · rw [law_done hc hs s hnext]
    simpa only [ae_dirac_eq, Filter.eventually_pure] using htop
termination_by s.denominator

decreasing_by exact s.next_lt hc hs hnext

private theorem indicator_credit (xs : List ℤ) (label : ℤ) (hxs : xs.Nodup) :
    (xs.map (fun i => if i = label then (1 : ℝ≥0∞) else 0)).sum =
      if label ∈ xs then 1 else 0 := by
  rw [← List.sum_toFinset _ hxs]
  simp

/-- Distinct labels have precisely their prescribed inclusion probabilities. -/
theorem inclusion_probability {size count : ℕ} (hc : 0 < count) (hs : count < size)
    (s : State size count) (hlabels : (s.items.map Prod.snd).Nodup) (label : ℤ) :
    law hc hs s {xs | label ∈ xs} =
      numeratorCredit s.items (fun i => if i = label then 1 else 0) / s.denominator := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet)]
  have heq : ∀ᵐ xs ∂law hc hs s,
      Set.indicator {xs : List ℤ | label ∈ xs} (1 : List ℤ → ℝ≥0∞) xs =
        (xs.map (fun i => if i = label then (1 : ℝ≥0∞) else 0)).sum := by
    filter_upwards [ae_nodup hc hs s hlabels] with xs hxs
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
      (indicator_credit xs label hxs).symm
  rw [lintegral_congr_ae heq]
  exact inclusion_expectation hc hs s _

end

end SampLib.SplittingPPS
