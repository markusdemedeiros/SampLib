module

public import SampLib.Distributions.ReservoirProcess
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! # The ordered law of Algorithm R

A selected initial item remains in its original slot. Conditional on the selected
subset, the selected later items occupy the remaining slots uniformly. Thus an
admissible tuple with m later items has mass 1 / (choose(n,k) * m!).
-/

open MeasureTheory Measure
open scoped ENNReal NNReal Classical

namespace SampLib.ReservoirLaw

noncomputable section

/-- The bounded tuples that can be stored after reading n stream positions. -/
def states (n k : ℕ) : Finset (Slots k) :=
  Fintype.piFinset (fun _ => Finset.range n)

@[simp] theorem mem_states (n k : ℕ) (s : Slots k) :
    s ∈ states n k ↔ ∀ i, s i < n := by
  simp [states, Fintype.mem_piFinset]

/-- Distinct selected positions, with each surviving initial position in its own slot. -/
def Admissible (n k : ℕ) (s : Slots k) : Prop :=
  (∀ i, s i < n) ∧ Function.Injective s ∧ ∀ i, s i < k → s i = i.val

/-- Number of selected positions arriving after the initial reservoir was filled. -/
def lateCount {k : ℕ} (s : Slots k) : ℕ :=
  (Finset.univ.filter (fun i => k ≤ s i)).card

def coefficient (n k : ℕ) (s : Slots k) : ℝ≥0 :=
  ((n.choose k : ℝ≥0) * (lateCount s).factorial)⁻¹

/-- Closed joint mass of the ordered reservoir slots. -/
def pmf (n k : ℕ) (s : Slots k) : ℝ≥0∞ :=
  if Admissible n k s then coefficient n k s else 0

/-- The independent closed-form law, before proving its reservoir transition identity. -/
def law (n k : ℕ) : Measure (Slots k) :=
  ∑ s ∈ states n k, pmf n k s • dirac s

theorem pmf_ne_top (n k : ℕ) (s : Slots k) : pmf n k s ≠ ∞ := by
  unfold pmf
  split_ifs <;> simp

instance (n k : ℕ) : IsFiniteMeasure (law n k) where
  measure_univ_lt_top := by
    simp only [law, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    exact ENNReal.sum_lt_top.mpr fun s _ => (pmf_ne_top n k s).lt_top

theorem law_singleton (n k : ℕ) (s : Slots k) : law n k {s} = pmf n k s := by
  simp only [law, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  by_cases hs : s ∈ states n k
  · simp [hs]
  · have ha : ¬ Admissible n k s := fun h => hs ((mem_states n k s).mpr h.1)
    simp [hs, pmf, ha]

theorem ae_admissible (n k : ℕ) : ∀ᵐ s ∂law n k, Admissible n k s := by
  apply ae_iff_of_countable.mpr
  intro s hs
  by_contra ha
  apply hs
  simp [law_singleton, pmf, ha]

/-- The initial reservoir stores each of its first k positions in its own slot. -/
def initial (k : ℕ) : Slots k := fun i => i.val

theorem admissible_initial (k : ℕ) : Admissible k k (initial k) :=
  ⟨fun i => i.isLt, Fin.val_injective, fun _ _ => rfl⟩

@[simp] theorem lateCount_initial (k : ℕ) : lateCount (initial k) = 0 := by
  unfold lateCount initial
  rw [Finset.filter_eq_empty_iff.mpr (fun i _ => Nat.not_le.mpr i.isLt)]
  rfl

private theorem admissible_at_capacity (k : ℕ) (s : Slots k) (h : Admissible k k s) :
    s = initial k := funext fun i => h.2.2 i (h.1 i)

/-- Before processing later arrivals, the reservoir is deterministic. -/
@[simp] theorem law_initial (k : ℕ) : law k k = dirac (initial k) := by
  apply Measure.ext_of_singleton
  intro s
  rw [law_singleton]
  by_cases hs : s = initial k
  · subst s
    simp [pmf, admissible_initial, coefficient]
  · have ha : ¬ Admissible k k s := fun h => hs (admissible_at_capacity k s h)
    simp [pmf, ha, Set.indicator, hs, eq_comm]

/-- The fresh ticket is independent and uniform, including its reject outcomes. -/
def tickets (n : ℕ) : Measure (Fin (n + 1)) := uniformOfFinset Finset.univ

instance (n : ℕ) : IsProbabilityMeasure (tickets n) :=
  isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

def step {k : ℕ} (n : ℕ) (s : Slots k) : Measure (Slots k) :=
  (tickets n).map (advance n s)

instance {k : ℕ} (n : ℕ) (s : Slots k) : IsProbabilityMeasure (step n s) where
  measure_univ := by
    rw [step, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem step_expectation {k : ℕ} (n : ℕ) (s : Slots k) (F : Slots k → ℝ≥0∞) :
    ∫⁻ t, F t ∂step n s = finish n 1 s F := by
  rw [step, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [tickets, uniformOfFinset, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum,
    finish_one, ENNReal.div_eq_inv_mul]

theorem Admissible.mono {n m k : ℕ} {s : Slots k} (h : Admissible n k s)
    (hnm : n ≤ m) : Admissible m k s :=
  ⟨fun i => (h.1 i).trans_le hnm, h.2⟩

/-- Fresh stream positions preserve distinctness and the fixed initial slots. -/
theorem admissible_advance {n k : ℕ} (hkn : k ≤ n) {s : Slots k}
    (h : Admissible n k s) (j : Fin (n + 1)) : Admissible (n + 1) k (advance n s j) := by
  by_cases hj : j.val < k
  · rw [advance_lt s j hj]
    let a : Fin k := ⟨j.val, hj⟩
    change Admissible (n + 1) k (Function.update s a n)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = a
      · subst i; simp
      · simp only [Function.update_of_ne hi]
        exact (h.1 i).trans_le (Nat.le_succ _)
    · intro i l hil
      by_cases hi : i = a <;> by_cases hl : l = a
      · exact hi.trans hl.symm
      · subst i
        simp only [Function.update_self, Function.update_of_ne hl] at hil
        have := h.1 l
        omega
      · subst l
        simp only [Function.update_self, Function.update_of_ne hi] at hil
        have := h.1 i
        omega
      · apply h.2.1
        simpa only [Function.update_of_ne hi, Function.update_of_ne hl] using hil
    · intro i hi
      by_cases hai : i = a
      · subst i; simp only [Function.update_self] at hi; omega
      · rw [Function.update_of_ne hai] at hi ⊢
        exact h.2.2 i hi
  · rw [advance_ge s j (by omega)]
    exact h.mono (Nat.le_succ _)

/-- Replacing one coordinate preserves injectivity exactly when its new value is fresh. -/
theorem injective_update_iff {k : ℕ} {s : Slots k} (hs : Function.Injective s)
    (j : Fin k) (x : ℕ) :
    Function.Injective (Function.update s j x) ↔ ∀ i, i ≠ j → s i ≠ x := by
  constructor
  · intro h i hi hx
    apply hi
    apply h
    simp [Function.update_of_ne hi, hx]
  · intro h i l hil
    by_cases hi : i = j <;> by_cases hl : l = j
    · exact hi.trans hl.symm
    · subst i
      simp only [Function.update_self, Function.update_of_ne hl] at hil
      exact (h l hl hil.symm).elim
    · subst l
      simp only [Function.update_self, Function.update_of_ne hi] at hil
      exact (h i hi hil).elim
    · apply hs
      simpa only [Function.update_of_ne hi, Function.update_of_ne hl] using hil

/-- Later positions available to restore the coordinate occupied by the newest item. -/
def available (n k : ℕ) (t : Slots k) : Finset ℕ :=
  (Finset.Ico k n).filter (fun x => ∀ i, t i ≠ x)

theorem admissible_predecessor {n k : ℕ} {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) (x : ℕ) (hx : x < n) :
    Admissible n k (Function.update t j x) ↔ x = j.val ∨ x ∈ available n k t := by
  have hother (i : Fin k) (hi : i ≠ j) : t i < n := by
    have hne : t i ≠ n := fun h => hi (ht.2.1 (h.trans hj.symm))
    have := ht.1 i
    omega
  constructor
  · intro h
    by_cases hxk : x < k
    · left
      simpa using h.2.2 j (by simpa using hxk)
    · right
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hx⟩, ?_⟩
      intro i hi
      by_cases hij : i = j
      · subst i; omega
      · have hneq := (injective_update_iff ht.2.1 j x).mp h.2.1 i hij
        exact hneq hi
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst i; simpa using hx
      · simpa only [Function.update_of_ne hi] using hother i hi
    · apply (injective_update_iff ht.2.1 j x).mpr
      intro i hi hix
      rcases h with rfl | h
      · have hti : t i < k := by omega
        have hpin := ht.2.2 i hti
        exact hi (Fin.ext (hpin.symm.trans hix))
      · exact (Finset.mem_filter.mp h).2 i hix
    · intro i hi
      by_cases hij : i = j
      · subst i
        simp only [Function.update_self] at hi ⊢
        rcases h with h | h
        · exact h
        · have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
          omega
      · rw [Function.update_of_ne hij] at hi ⊢
        exact ht.2.2 i hi

theorem lateCount_update_late {k : ℕ} (t : Slots k) (j : Fin k) (x : ℕ)
    (hj : k ≤ t j) (hx : k ≤ x) :
    lateCount (Function.update t j x) = lateCount t := by
  unfold lateCount
  congr 1
  ext i
  by_cases hi : i = j <;> simp [hi, hj, hx]

theorem lateCount_update_initial {k : ℕ} (t : Slots k) (j : Fin k) (hj : k ≤ t j) :
    lateCount (Function.update t j j.val) = lateCount t - 1 := by
  have he : Finset.univ.filter (fun i => k ≤ Function.update t j j.val i) =
      (Finset.univ.filter (fun i => k ≤ t i)).erase j := by
    ext i
    by_cases hi : i = j <;> simp [hi, j.isLt]
  unfold lateCount
  rw [he, Finset.card_erase_of_mem (by simp [hj])]

theorem lateCount_le {n k : ℕ} {t : Slots k} (ht : Admissible n k t) :
    lateCount t ≤ n - k := by
  let late := Finset.univ.filter (fun i => k ≤ t i)
  have hsub : late.image t ⊆ Finset.Ico k n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, ht.1 i⟩
  simpa [late, lateCount, Nat.card_Ico, Finset.card_image_of_injective _ ht.2.1] using
    Finset.card_le_card hsub

/-- All previous later items except the newest occupy distinct forbidden values. -/
theorem available_card {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) :
    (available n k t).card = n + 1 - k - lateCount t := by
  let old := (Finset.univ.filter (fun i => k ≤ t i)).erase j
  have hjmem : j ∈ Finset.univ.filter (fun i => k ≤ t i) := by simp [hj, hkn]
  have hold : old.card = lateCount t - 1 := Finset.card_erase_of_mem hjmem
  have hsub : old.image t ⊆ Finset.Ico k n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hij, hi⟩ := Finset.mem_erase.mp hi
    have hlt := ht.1 i
    have hne : t i ≠ n := fun h => hij (ht.2.1 (h.trans hj.symm))
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, by omega⟩
  have he : available n k t = Finset.Ico k n \ old.image t := by
    ext x
    simp only [available, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun ⟨i, _, hi⟩ => hall i hi⟩
    · rintro ⟨hx, hnone⟩
      refine ⟨hx, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst i
        have := (Finset.mem_Ico.mp hx).2
        omega
      · apply hnone
        refine ⟨i, Finset.mem_erase.mpr ⟨hij, ?_⟩, hi⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have := (Finset.mem_Ico.mp hx).1
          omega⟩
  have himage : (old.image t).card = lateCount t - 1 := by
    rw [Finset.card_image_of_injective _ ht.2.1, hold]
  have hbound := Finset.card_le_card hsub
  have hm : 0 < lateCount t := by
    exact Finset.card_pos.mpr ⟨j, hjmem⟩
  rw [he, Finset.card_sdiff_of_subset hsub, himage, Nat.card_Ico]
  rw [Nat.card_Ico, himage] at hbound
  omega

def weight (n k : ℕ) (s : Slots k) : ℝ≥0 :=
  if Admissible n k s then coefficient n k s else 0

theorem pmf_eq_coe_weight (n k : ℕ) (s : Slots k) : pmf n k s = weight n k s := by
  simp only [pmf, weight]
  split_ifs <;> simp

/-- Binomial counting supplies the common factor in both transition cases. -/
theorem coefficient_step {n k : ℕ} (hkn : k ≤ n) (t : Slots k) :
    ((n + 1 - k : ℕ) : ℝ≥0) * coefficient n k t / (n + 1 : ℕ) =
      coefficient (n + 1) k t := by
  have hc : (n.choose k : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  have hc' : ((n + 1).choose k : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hkn.trans (Nat.le_succ n))).ne'
  have hf : ((lateCount t).factorial : ℝ≥0) ≠ 0 := by positivity
  have hn : (n + 1 : ℝ≥0) ≠ 0 := by positivity
  have hchoose : (n.choose k : ℝ≥0) * (n + 1) =
      ((n + 1).choose k : ℝ≥0) * (n + 1 - k : ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n k
  unfold coefficient
  field_simp
  simp only [Nat.cast_add, Nat.cast_one] at *
  simpa [mul_comm] using hchoose.symm

/-- The initial-coordinate predecessor carries m times the mass of a later predecessor. -/
theorem coefficient_restore_initial {n k : ℕ} {t : Slots k} (j : Fin k)
    (hj : k ≤ t j) :
    coefficient n k (Function.update t j j.val) =
      (lateCount t : ℝ≥0) * coefficient n k t := by
  have hm : 0 < lateCount t := Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  have hfac : (lateCount t).factorial = lateCount t * (lateCount t - 1).factorial := by
    simpa [Nat.sub_add_cancel hm] using Nat.factorial_succ (lateCount t - 1)
  simp only [coefficient, lateCount_update_initial t j hj, hfac, Nat.cast_mul]
  by_cases hc : n.choose k = 0
  · simp [hc]
  · have hc' : (n.choose k : ℝ≥0) ≠ 0 := by exact_mod_cast hc
    have hm' : (lateCount t : ℝ≥0) ≠ 0 := by positivity
    have hf : ((lateCount t - 1).factorial : ℝ≥0) ≠ 0 := by positivity
    field_simp

/-- With m later items, the initial predecessor has mass m·b; the n+1−k−m missing later
predecessors each have mass b. The total incoming mass is therefore (n+1−k)·b. -/
theorem predecessor_weight_sum {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (ht : Admissible (n + 1) k t) (j : Fin k) (hj : t j = n) :
    ∑ x ∈ Finset.range n, weight n k (Function.update t j x) =
      ((n + 1 - k : ℕ) : ℝ≥0) * coefficient n k t := by
  let a := coefficient n k (Function.update t j j.val)
  let b := coefficient n k t
  have hform (x : ℕ) (hx : x ∈ Finset.range n) :
      weight n k (Function.update t j x) =
        (if x = j.val then a else 0) + (if x ∈ available n k t then b else 0) := by
    have hx' := Finset.mem_range.mp hx
    rw [weight, admissible_predecessor ht j hj x hx']
    by_cases hxj : x = j.val
    · subst x
      have hnot : j.val ∉ available n k t := by
        intro h
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
        omega
      simp [hnot, a]
    · by_cases hxa : x ∈ available n k t
      · have hxk := (Finset.mem_Ico.mp (Finset.mem_filter.mp hxa).1).1
        simp [hxj, hxa, coefficient, lateCount_update_late t j x (by omega) hxk, b]
      · simp [hxj, hxa]
  rw [Finset.sum_congr rfl hform, Finset.sum_add_distrib]
  have hav : available n k t ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
  have hfilter : (Finset.range n).filter (fun x => x ∈ available n k t) =
      available n k t := by
    ext x
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hav h, h⟩⟩
  have hfirst : (∑ x ∈ Finset.range n, if x = j.val then a else 0) = a := by
    simp [j.isLt.trans_le hkn]
  have hsecond : (∑ x ∈ Finset.range n, if x ∈ available n k t then b else 0) =
      (available n k t).card * b := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [hfirst, hsecond]
  rw [show a = (lateCount t : ℝ≥0) * b from
    coefficient_restore_initial j (by omega), available_card hkn ht j hj]
  have hm : lateCount t ≤ n + 1 - k := lateCount_le ht
  rw [← add_mul]
  congr 1
  exact_mod_cast Nat.add_sub_of_le hm

theorem admissible_of_weight_ne_zero {n k : ℕ} {s : Slots k}
    (h : weight n k s ≠ 0) : Admissible n k s := by
  by_contra ha
  exact h (by simp [weight, ha])

/-- Every incoming tuple is admissible, including when the newest item replaces a slot. -/
theorem admissible_of_predecessor {n k : ℕ} (hkn : k ≤ n) {t : Slots k}
    (j : Fin k) (hj : t j = n) (x : ℕ) (h : Admissible n k (Function.update t j x)) :
    Admissible (n + 1) k t := by
  let ticket : Fin (n + 1) := ⟨j.val, j.isLt.trans_le (hkn.trans (Nat.le_succ n))⟩
  have he : advance n (Function.update t j x) ticket = t := by
    rw [advance_lt _ _ j.isLt]
    change Function.update (Function.update t j x) j n = t
    rw [Function.update_idem, ← hj, Function.update_eq_self]
  rw [← he]
  exact admissible_advance hkn h ticket

/-- The incoming mass is the same in both cases: reject the new item, or restore its slot. -/
theorem incoming_weight {n k : ℕ} (hkn : k ≤ n) (t : Slots k) :
    (((n + 1 - k : ℕ) : ℝ≥0) * weight n k t +
      ∑ j : Fin k, if t j = n then
        ∑ x ∈ Finset.range n, weight n k (Function.update t j x) else 0) / (n + 1 : ℕ) =
      weight (n + 1) k t := by
  by_cases ht : Admissible (n + 1) k t
  · by_cases hnew : ∃ j, t j = n
    · obtain ⟨j, hj⟩ := hnew
      have hold : ¬ Admissible n k t := fun h => Nat.lt_irrefl n (hj ▸ h.1 j)
      have he (i : Fin k) : t i = n ↔ i = j :=
        ⟨fun hi => ht.2.1 (hi.trans hj.symm), fun hi => hi ▸ hj⟩
      rw [show weight n k t = 0 by simp [weight, hold],
        show weight (n + 1) k t = coefficient (n + 1) k t by simp [weight, ht]]
      simp only [mul_zero, zero_add, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [predecessor_weight_sum hkn ht j hj]
      exact coefficient_step hkn t
    · have hold : Admissible n k t := by
        refine ⟨fun i => ?_, ht.2⟩
        have hi := ht.1 i
        have hn : t i ≠ n := fun h => hnew ⟨i, h⟩
        omega
      have hall (j : Fin k) : t j ≠ n := fun h => hnew ⟨j, h⟩
      simpa only [weight, hold, ht, hall, ite_true, ite_false, Finset.sum_const_zero,
        add_zero] using coefficient_step hkn t
  · have hold : ¬ Admissible n k t := fun h => ht (h.mono (Nat.le_succ n))
    have hzero (j : Fin k) : (if t j = n then
        ∑ x ∈ Finset.range n, weight n k (Function.update t j x) else 0) = 0 := by
      split_ifs with hj
      · apply Finset.sum_eq_zero
        intro x _
        by_contra hx
        exact ht (admissible_of_predecessor hkn j hj x (admissible_of_weight_ne_zero hx))
      · rfl
    rw [show weight n k t = 0 by simp [weight, hold],
      show weight (n + 1) k t = 0 by simp [weight, ht]]
    simp only [hzero, Finset.sum_const_zero, mul_zero, zero_add, zero_div]

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

