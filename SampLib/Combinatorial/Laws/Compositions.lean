import SampLib.Combinatorial.Support.IntegerRange
import SampLib.Combinatorial.SampleInOrder

/-! # Uniform compositions from interior cuts

Consecutive gaps biject increasing interior cut lists with positive compositions.
Subtracting one from every part gives the corresponding weak composition.
-/

open MeasureTheory Measure
open scoped ENNReal Classical

namespace SampLib.Compositions

noncomputable section

local instance : MeasurableSpace (List ℤ) := ⊤

/-- Consecutive gaps, including the final gap to the right endpoint. -/
def gaps (total prev : ℤ) : List ℤ → List ℤ
  | [] => [total - prev]
  | x :: xs => (x - prev) :: gaps total x xs

/-- Positive ordered parts of a prescribed length and total. -/
def positive (n total : ℕ) (parts : List ℤ) : Prop :=
  parts.length = n ∧ (∀ x ∈ parts, 0 < x) ∧ parts.sum = (total : ℤ)

/-- Recover the interior partial sums, omitting the final endpoint. -/
def cutPoints (prev : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => if xs = [] then [] else (prev + x) :: cutPoints (prev + x) xs

@[simp] theorem gaps_length (total prev : ℤ) (cuts : List ℤ) :
    (gaps total prev cuts).length = cuts.length + 1 := by
  induction cuts generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [gaps, ih]

@[simp] theorem gaps_sum (total prev : ℤ) (cuts : List ℤ) :
    (gaps total prev cuts).sum = total - prev := by
  induction cuts generalizing prev with
  | nil => simp [gaps]
  | cons x xs ih => simp only [gaps, List.sum_cons, ih]; omega

theorem gaps_ne_nil (total prev : ℤ) (cuts : List ℤ) : gaps total prev cuts ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

@[simp] theorem cutPoints_gaps (total prev : ℤ) (cuts : List ℤ) :
    cutPoints prev (gaps total prev cuts) = cuts := by
  induction cuts generalizing prev with
  | nil => simp [gaps, cutPoints]
  | cons x xs ih =>
    simp only [gaps, cutPoints, gaps_ne_nil, ite_false]
    rw [show prev + (x - prev) = x by omega, ih]

theorem gaps_injective (total prev : ℤ) : Function.Injective (gaps total prev) := by
  intro xs ys h
  simpa using congrArg (cutPoints prev) h

@[simp] theorem cutPoints_length (prev : ℤ) (parts : List ℤ) :
    (cutPoints prev parts).length = parts.length - 1 := by
  induction parts generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [cutPoints]
    | cons y ys =>
      rw [cutPoints]
      simp only [List.cons_ne_nil, ite_false, List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem gaps_cutPoints (total prev : ℤ) (parts : List ℤ) (hne : parts ≠ [])
    (hs : parts.sum = total - prev) : gaps total prev (cutPoints prev parts) = parts := by
  induction parts generalizing prev with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simpa [gaps, cutPoints] using hs.symm
    | cons y ys =>
      have ht : (y :: ys).sum = total - (prev + x) := by
        simp only [List.sum_cons] at hs ⊢
        omega
      rw [cutPoints]
      simp only [List.cons_ne_nil, ite_false]
      rw [gaps, show prev + x - prev = x by omega, ih (prev + x) (by simp) ht]

/-- Strictly increasing cuts between the two endpoints. -/
def within (prev total : ℤ) : List ℤ → Prop
  | [] => prev < total
  | x :: xs => prev < x ∧ within x total xs

theorem within_bounds (prev total : ℤ) (cuts : List ℤ) (h : within prev total cuts) :
    prev < total ∧ ∀ x ∈ cuts, prev < x ∧ x < total := by
  induction cuts generalizing prev with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    obtain ⟨hpx, htail⟩ := h
    obtain ⟨hxt, hb⟩ := ih x htail
    refine ⟨hpx.trans hxt, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpx, hxt⟩
    · exact ⟨hpx.trans (hb y hy).1, (hb y hy).2⟩

theorem within_mono_left {prev next total : ℤ} {cuts : List ℤ}
    (h : within next total cuts) (hp : prev ≤ next) : within prev total cuts := by
  cases cuts with
  | nil => exact hp.trans_lt h
  | cons x xs => exact ⟨hp.trans_lt h.1, h.2⟩

theorem within_sublist {xs ys : List ℤ} (h : xs.Sublist ys) {prev total : ℤ}
    (hy : within prev total ys) : within prev total xs := by
  induction h generalizing prev with
  | slnil => exact hy
  | cons x h ih => exact within_mono_left (ih hy.2) hy.1.le
  | cons_cons x h ih => exact ⟨hy.1, ih hy.2⟩

theorem gaps_positive (total prev : ℤ) (cuts : List ℤ) :
    (∀ x ∈ gaps total prev cuts, 0 < x) ↔ within prev total cuts := by
  induction cuts generalizing prev with
  | nil => simp [gaps, within]
  | cons x xs ih => simp [gaps, within, ih]

theorem cutPoints_within (total prev : ℤ) (parts : List ℤ) (hne : parts ≠ [])
    (hp : ∀ x ∈ parts, 0 < x) (hs : parts.sum = total - prev) :
    within prev total (cutPoints prev parts) := by
  induction parts generalizing prev with
  | nil => contradiction
  | cons x xs ih =>
    have hx := hp x (by simp)
    cases xs with
    | nil =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      simpa [cutPoints, within] using (by omega : prev < total)
    | cons y ys =>
      have ht : (y :: ys).sum = total - (prev + x) := by
        simp only [List.sum_cons] at hs ⊢
        omega
      simp only [cutPoints, List.cons_ne_nil, ite_false, within]
      exact ⟨by omega, ih (prev + x) (by simp) (fun z hz => hp z (by simp [hz])) ht⟩

theorem interval_length (lo : ℤ) (n : ℕ) : (IntegerRange.interval lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp [IntegerRange.interval, ih]

theorem interval_within (lo : ℤ) (n : ℕ) :
    within (lo - 1) (lo + n) (IntegerRange.interval lo n) := by
  induction n generalizing lo with
  | zero => simp [IntegerRange.interval, within]
  | succ n ih =>
    change lo - 1 < lo ∧ within lo (lo + ((n + 1 : ℕ) : ℤ))
      (IntegerRange.interval (lo + 1) n)
    refine ⟨by omega, ?_⟩
    have he : lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + n := by push_cast; ring
    rw [he]
    simpa using ih (lo + 1)

theorem within_nodup (prev total : ℤ) (cuts : List ℤ) (h : within prev total cuts) :
    cuts.Nodup := by
  induction cuts generalizing prev with
  | nil => simp
  | cons x xs ih =>
    refine List.nodup_cons.mpr ⟨?_, ih x h.2⟩
    intro hx
    have := (within_bounds x total xs h.2).2 x hx
    omega

theorem sublist_interval_of_within (lo : ℤ) (n : ℕ) (cuts : List ℤ)
    (h : within (lo - 1) (lo + n) cuts) : cuts.Sublist (IntegerRange.interval lo n) := by
  induction n generalizing lo cuts with
  | zero =>
    cases cuts with
    | nil => simp
    | cons x xs =>
      have hb := (within_bounds (lo - 1) (lo + 0) (x :: xs) h).2 x (by simp)
      omega
  | succ n ih =>
    cases cuts with
    | nil => simp
    | cons x xs =>
      have hb := (within_bounds (lo - 1) (lo + ((n + 1 : ℕ) : ℤ)) (x :: xs) h).2 x
        (by simp)
      have he : lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + n := by push_cast; ring
      by_cases hx : x = lo
      · subst x
        apply List.Sublist.cons_cons
        apply ih (lo + 1) xs
        simpa only [add_sub_cancel_right, ← he] using h.2
      · apply List.Sublist.cons
        apply ih (lo + 1) (x :: xs)
        simp only [add_sub_cancel_right]
        change lo < x ∧ within x ((lo + 1) + n) xs
        exact ⟨by omega, he ▸ h.2⟩

theorem interior_iff_sublist (total : ℕ) (ht : 0 < total) (cuts : List ℤ) :
    within 0 total cuts ↔ cuts.Sublist (IntegerRange.interval 1 (total - 1)) := by
  have he : (1 : ℤ) + (total - 1 : ℕ) = total := by omega
  constructor
  · intro h
    apply sublist_interval_of_within
    simpa [he] using h
  · intro h
    have hw := within_sublist h (interval_within 1 (total - 1))
    simpa [he] using hw

/-- Enumerate every positive composition once by its increasing interior cuts. -/
def enumeration (n total : ℕ) : List (List ℤ) :=
  ((IntegerRange.interval 1 (total - 1)).sublistsLen (n - 1)).map (gaps total 0)

theorem enumeration_nodup (n total : ℕ) : (enumeration n total).Nodup :=
  List.Nodup.map (gaps_injective total 0) (List.nodup_sublistsLen _
    (within_nodup _ _ _ (interval_within 1 (total - 1))))

@[simp] theorem enumeration_length (n total : ℕ) :
    (enumeration n total).length = (total - 1).choose (n - 1) := by
  simp [enumeration, interval_length]

/-- The cut enumeration is exactly all positive ordered `n`-part compositions. -/
theorem mem_enumeration (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) (parts : List ℤ) :
    parts ∈ enumeration n total ↔ positive n total parts := by
  have ht0 : 0 < total := lt_of_lt_of_le hn ht
  constructor
  · intro h
    obtain ⟨cuts, hc, rfl⟩ := List.mem_map.mp h
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hc
    refine ⟨?_, (gaps_positive _ _ _).mpr ((interior_iff_sublist total ht0 cuts).mpr hsub), ?_⟩
    · rw [gaps_length, hlen]
      omega
    · simp
  · rintro ⟨hlen, hp, hs⟩
    have hne : parts ≠ [] := by intro he; subst parts; simp at hlen; omega
    apply List.mem_map.mpr
    refine ⟨cutPoints 0 parts, List.mem_sublistsLen.mpr ⟨?_, ?_⟩, ?_⟩
    · apply (interior_iff_sublist total ht0 _).mp
      apply cutPoints_within _ _ parts hne hp
      simpa using hs
    · simp [hlen]
    · apply gaps_cutPoints _ _ parts hne
      simpa using hs

private theorem cut_count_le (n total : ℕ) (h : n ≤ total) :
    n - 1 ≤ (IntegerRange.interval 1 (total - 1)).length := by
  rw [interval_length]
  omega

/-- Choose the interior cuts uniformly and take their consecutive gaps. -/
def law (n total : ℕ) (_hn : 0 < n) (ht : n ≤ total) : Measure (List ℤ) :=
  (SampleInOrder.law (IntegerRange.interval 1 (total - 1)) (n - 1)
    (cut_count_le n total ht)).map (gaps total 0)

instance (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    IsProbabilityMeasure (law n total hn ht) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The cut-to-gap bijection transports every continuation expectation. -/
theorem expectation (n total : ℕ) (hn : 0 < n) (ht : n ≤ total)
    (F : List ℤ → ℝ≥0∞) :
    ∫⁻ cuts, F (gaps total 0 cuts) ∂SampleInOrder.law
      (IntegerRange.interval 1 (total - 1)) (n - 1) (cut_count_le n total ht) =
      ∫⁻ parts, F parts ∂law n total hn ht := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

private theorem sum_dirac_preimage (xs : List (List ℤ)) (f : List ℤ → List ℤ)
    (parts : List ℤ) :
    ((xs.map (dirac : List ℤ → Measure (List ℤ))).sum) (f ⁻¹' {parts}) =
      ((xs.map f).count parts : ℝ≥0∞) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : f x = parts <;>
      simp [Set.indicator, h, ih, add_comm]

/-- Every positive composition has reciprocal binomial-coefficient mass. -/
theorem law_singleton (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) (parts : List ℤ) :
    law n total hn ht {parts} =
      if positive n total parts then ((total - 1).choose (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  simp only [SampleInOrder.law, Measure.smul_apply, smul_eq_mul, sum_dirac_preimage]
  change ((IntegerRange.interval 1 (total - 1)).length.choose (n - 1) : ℝ≥0∞)⁻¹ *
    ((enumeration n total).count parts : ℝ≥0∞) = _
  rw [interval_length]
  by_cases hp : positive n total parts
  · rw [ite_eq_left hp, List.count_eq_one_of_mem (enumeration_nodup n total)
      ((mem_enumeration n total hn ht parts).mpr hp)]
    simp
  · rw [ite_eq_right hp, List.count_eq_zero_of_not_mem
      (fun h => hp ((mem_enumeration n total hn ht parts).mp h))]
    simp

/-- The cut-gap enumeration realizes the usual uniform finite-set law. -/
theorem law_eq_uniform (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    law n total hn ht = uniformOfFinset (enumeration n total).toFinset := by
  apply Measure.ext_of_singleton
  intro parts
  rw [law_singleton, uniformOfFinset_apply_singleton]
  simp only [List.mem_toFinset, mem_enumeration n total hn ht,
    List.toFinset_card_of_nodup (enumeration_nodup n total), enumeration_length]

/-- Weak compositions have nonnegative ordered parts of the prescribed total. -/
def weak (n total : ℕ) (parts : List ℤ) : Prop :=
  parts.length = n ∧ (∀ x ∈ parts, 0 ≤ x) ∧ parts.sum = (total : ℤ)

def addOne (parts : List ℤ) : List ℤ := parts.map (· + 1)

def subtractOne (parts : List ℤ) : List ℤ := parts.map (· - 1)

@[simp] theorem addOne_subtractOne (parts : List ℤ) : addOne (subtractOne parts) = parts := by
  simp [addOne, subtractOne, List.map_map, Function.comp_def]

@[simp] theorem subtractOne_addOne (parts : List ℤ) : subtractOne (addOne parts) = parts := by
  simp [addOne, subtractOne, List.map_map, Function.comp_def]

theorem sum_addOne (parts : List ℤ) : (addOne parts).sum = parts.sum + parts.length := by
  simp [addOne, List.sum_map_add]

/-- Adding one to every part is the stars-and-bars bijection. -/
theorem positive_addOne_iff (n total : ℕ) (parts : List ℤ) :
    positive n (total + n) (addOne parts) ↔ weak n total parts := by
  unfold positive weak
  rw [show (addOne parts).length = parts.length by simp [addOne], sum_addOne]
  constructor
  · rintro ⟨hl, hp, hs⟩
    refine ⟨hl, ?_, ?_⟩
    · intro x hx
      have := hp (x + 1) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      omega
    · push_cast at hs
      omega
  · rintro ⟨hl, hp, hs⟩
    refine ⟨hl, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hp y hy
      omega
    · push_cast
      omega

/-- Uniform weak compositions, obtained by subtracting one from every positive part. -/
def weakLaw (n total : ℕ) (hn : 0 < n) : Measure (List ℤ) :=
  (law n (total + n) hn (by omega)).map subtractOne

instance (n total : ℕ) (hn : 0 < n) : IsProbabilityMeasure (weakLaw n total hn) where
  measure_univ := by
    rw [weakLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

theorem weak_expectation (n total : ℕ) (hn : 0 < n) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ parts, F (subtractOne parts) ∂law n (total + n) hn (by omega) =
      ∫⁻ parts, F parts ∂weakLaw n total hn := by
  rw [weakLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Every weak composition has the same stars-and-bars probability. -/
theorem weakLaw_singleton (n total : ℕ) (hn : 0 < n) (parts : List ℤ) :
    weakLaw n total hn {parts} =
      if weak n total parts then ((total + n - 1).choose (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  have hpre : subtractOne ⁻¹' {parts} = {addOne parts} := by
    ext xs
    change subtractOne xs = parts ↔ xs = addOne parts
    constructor
    · intro h
      simpa using congrArg addOne h
    · rintro rfl
      simp
  rw [weakLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, law_singleton, positive_addOne_iff]

end

end SampLib.Compositions
