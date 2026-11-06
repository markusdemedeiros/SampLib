import SampLib.Uniform.UniformInt

/-! # The joint law of systematic probability-proportional-to-size sampling

One uniform integer shift determines all selected labels. Writing the law as the
pushforward of this single shift keeps the dependence between labels explicit.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.SystematicPPS

noncomputable section

/-- Labels crossed by a translated cumulative-weight lattice. -/
def select (count total ticket : ℤ) : List ℕ → ℤ → ℤ → List ℤ
  | [], _, _ => []
  | w :: ws, before, label =>
      let after := before + count * w
      let rest := select count total ticket ws after (label + 1)
      if (before + ticket) / total < (after + ticket) / total then label :: rest else rest

/-- A cell of width at most one lattice period crosses at most one lattice point. -/
private theorem quotient_step (a width total : ℤ) (ht : 0 < total)
    (hw : 0 ≤ width) (hcap : width ≤ total) :
    a / total ≤ (a + width) / total ∧ (a + width) / total ≤ a / total + 1 := by
  constructor
  · exact Int.ediv_le_ediv ht (by omega)
  · have h := Int.ediv_le_ediv ht (show a + width ≤ a + total by omega)
    simpa only [Int.add_ediv_of_dvd_right (dvd_refl total), Int.ediv_self ht.ne'] using h

/-- Across one full period, a unit displacement crosses exactly one lattice point. -/
private theorem unit_crossings (before : ℤ) (total : ℕ) (ht : 0 < total) :
    ∑ t ∈ Finset.range total,
      ((before + (t : ℤ) + 1) / total - (before + t) / total) = 1 := by
  have h := Finset.sum_range_sub (fun t : ℕ => (before + t) / (total : ℤ)) total
  have hcast (t : ℕ) : before + (↑(t + 1) : ℤ) = before + t + 1 := by omega
  simp only [hcast, Nat.cast_zero, add_zero] at h
  rw [Int.add_ediv_of_dvd_right (dvd_refl (total : ℤ)),
    Int.ediv_self (by exact_mod_cast ht.ne' : (total : ℤ) ≠ 0)] at h
  simpa using h

/-- Translating a cell of integer width crosses that many lattice points in a full period. -/
theorem crossing_sum (before : ℤ) (width total : ℕ) (ht : 0 < total) :
    ∑ t ∈ Finset.range total,
      ((before + width + t) / (total : ℤ) - (before + t) / total) = width := by
  induction width with
  | zero => simp
  | succ width ih =>
    have hunit := unit_crossings (before + width) total ht
    have hadd (t : ℕ) :
        (before + (↑(width + 1) : ℤ) + t) / (total : ℤ) - (before + t) / total =
          ((before + width + t) / (total : ℤ) - (before + t) / total) +
          ((before + width + t + 1) / (total : ℤ) - (before + width + t) / total) := by
      have : before + (↑(width + 1) : ℤ) + t = before + width + t + 1 := by omega
      rw [this]
      omega
    simp_rw [hadd]
    rw [Finset.sum_add_distrib, ih, hunit]
    simp

/-- Exactly `width` of the possible shifts cross a cell of that width. -/
theorem crossing_count (before : ℤ) (width total : ℕ) (ht : 0 < total)
    (hcap : width ≤ total) :
    (∑ t ∈ Finset.range total,
      if (before + (t : ℤ)) / total < (before + width + t) / total then (1 : ℕ) else 0) =
      width := by
  have ht' : (0 : ℤ) < total := by exact_mod_cast ht
  have hone (t : ℕ) :
      (if (before + (t : ℤ)) / total < (before + width + t) / total then (1 : ℤ) else 0) =
        (before + width + t) / total - (before + t) / total := by
    have hstep := quotient_step (before + t) width total ht' (Int.natCast_nonneg _)
      (by exact_mod_cast hcap)
    have hs : before + (t : ℤ) + width = before + width + t := by ring
    rw [hs] at hstep
    split_ifs <;> omega
  have hsum : (∑ t ∈ Finset.range total,
      if (before + (t : ℤ)) / total < (before + width + t) / total then (1 : ℤ) else 0) =
      (width : ℤ) := by
    simp_rw [hone]
    exact crossing_sum before width total ht
  exact_mod_cast hsum

/-- Counting crossings telescopes along cumulative weights. -/
theorem length_select (ws : List ℕ) (count total ticket before label : ℤ)
    (hc : 0 ≤ count) (ht : 0 < total) (hcap : ∀ w ∈ ws, count * w ≤ total) :
    ((select count total ticket ws before label).length : ℤ) =
      (before + count * ws.sum + ticket) / total - (before + ticket) / total := by
  induction ws generalizing before label with
  | nil => simp [select]
  | cons w ws ih =>
    have htail : ∀ a ∈ ws, count * a ≤ total := fun a ha => hcap a (by simp [ha])
    have hstep := quotient_step (before + ticket) (count * w) total ht
      (mul_nonneg hc (Int.natCast_nonneg _)) (hcap w (by simp))
    have hrest := ih (before + count * w) (label + 1) htail
    have hfinal : before + count * (↑(w :: ws).sum : ℤ) + ticket =
        before + count * w + count * ws.sum + ticket := by
      simp only [List.sum_cons, Nat.cast_add]
      ring
    simp only [select]
    split_ifs with h
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, hfinal]
      rw [hrest]
      have hinc : (before + count * w + ticket) / total = (before + ticket) / total + 1 := by
        have hs : before + ticket + count * w = before + count * w + ticket := by ring
        rw [hs] at hstep
        omega
      omega
    · simp only [hfinal]
      rw [hrest]
      have heq : (before + count * w + ticket) / total = (before + ticket) / total := by
        have hs : before + ticket + count * w = before + count * w + ticket := by ring
        rw [hs] at hstep
        omega
      omega

/-- Every admissible uniform shift produces exactly the requested sample size. -/
theorem sample_length (ws : List ℕ) (count ticket : ℕ) (ht : 0 < ws.sum)
    (hticket : ticket < ws.sum) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    (select count ws.sum ticket ws 0 0).length = count := by
  have h := length_select ws count ws.sum ticket 0 0 (Int.natCast_nonneg _)
    (by exact_mod_cast ht) (fun w hw => by exact_mod_cast hcap w hw)
  have hz : (ticket : ℤ) / ws.sum = 0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hticket)
  simp only [zero_add, Int.mul_add_ediv_right (count : ℤ) (ticket : ℤ)
      (by exact_mod_cast ht.ne' : (ws.sum : ℤ) ≠ 0), hz,
    add_zero, sub_zero] at h
  exact_mod_cast h

/-- Selected labels retain their original positions. -/
theorem mem_bounds (ws : List ℕ) (count total ticket before label x : ℤ)
    (hx : x ∈ select count total ticket ws before label) :
    label ≤ x ∧ x < label + ws.length := by
  induction ws generalizing before label with
  | nil => simp [select] at hx
  | cons w ws ih =>
    simp only [select] at hx
    split_ifs at hx with h
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      · have hb := ih _ _ hx
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
    · have hb := ih _ _ hx
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- A label is selected exactly when its cumulative-weight interval crosses the shifted lattice. -/
theorem mem_select (ws : List ℕ) (count total ticket before label : ℤ)
    (i : ℕ) (hi : i < ws.length) :
    label + i ∈ select count total ticket ws before label ↔
      (before + count * (ws.take i).sum + ticket) / total <
        (before + count * (ws.take (i + 1)).sum + ticket) / total := by
  induction ws generalizing i before label with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      have hn : label ∉ select count total ticket ws (before + count * w) (label + 1) := by
        intro hm
        have hb := mem_bounds ws count total ticket (before + count * w) (label + 1) label hm
        omega
      simp only [Nat.cast_zero, add_zero, List.take_zero, List.sum_nil, mul_zero,
        Nat.zero_add, List.take_one, select]
      split_ifs <;> simp_all
    | succ i =>
      have hi' : i < ws.length := by simpa using hi
      have hrec := ih (before + count * w) (label + 1) i hi'
      have hlabel : label + (↑(i + 1) : ℤ) = label + 1 + i := by omega
      have hne : label + 1 + (i : ℤ) ≠ label := by omega
      have hleft : before + count * (↑((w :: ws).take (i + 1)).sum : ℤ) + ticket =
          before + count * w + count * (ws.take i).sum + ticket := by
        simp only [List.take_succ_cons, List.sum_cons, Nat.cast_add]
        ring
      have hright : before + count * (↑((w :: ws).take (i + 1 + 1)).sum : ℤ) + ticket =
          before + count * w + count * (ws.take (i + 1)).sum + ticket := by
        simp only [List.take_succ_cons, List.sum_cons, Nat.cast_add]
        ring
      rw [hleft, hright, ← hrec]
      simp only [select]
      split_ifs <;> simp only [List.mem_cons, hlabel, hne, false_or]

/-- Each item's inclusion frequency is its prescribed numerator. -/
theorem inclusion_count (ws : List ℕ) (count i : ℕ) (hi : i < ws.length)
    (ht : 0 < ws.sum) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    (∑ t ∈ Finset.range ws.sum,
      if (i : ℤ) ∈ select count ws.sum t ws 0 0 then (1 : ℕ) else 0) = count * ws[i] := by
  have hcondition (t : ℕ) :
      (i : ℤ) ∈ select count ws.sum t ws 0 0 ↔
        ((count : ℤ) * (ws.take i).sum + t) / ws.sum <
          ((count : ℤ) * (ws.take i).sum + (count * ws[i] : ℕ) + t) / ws.sum := by
    have h := mem_select ws count ws.sum t 0 0 i hi
    simp only [zero_add] at h
    rw [List.take_succ_eq_append_getElem hi, List.sum_append, List.sum_singleton] at h
    have heq : (count : ℤ) * ((ws.take i).sum + ws[i] : ℕ) + t =
        (count : ℤ) * (ws.take i).sum + (count * ws[i] : ℕ) + t := by
      push_cast
      ring
    rw [heq] at h
    exact h
  simp_rw [hcondition]
  exact crossing_count ((count : ℤ) * (ws.take i).sum) (count * ws[i]) ws.sum ht
    (hcap ws[i] (List.getElem_mem hi))

/-- Every sample uses the same shift for all labels. -/
def law (ws : List ℕ) (count : ℕ) : Measure (List ℤ) :=
  (UniformInt.law ws.sum).map (fun t : ℕ => select count ws.sum t ws 0 0)

instance (ws : List ℕ) (count : ℕ) [NeZero ws.sum] :
    IsProbabilityMeasure (law ws count) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem select_zero (total ticket before label : ℤ) (ws : List ℕ) :
    select 0 total ticket ws before label = [] := by
  induction ws generalizing before label with
  | nil => rfl
  | cons w ws ih => simp [select, ih]

@[simp] theorem law_zero (ws : List ℕ) [NeZero ws.sum] : law ws 0 = Measure.dirac [] := by
  simp [law, select_zero, Measure.map_const]

/-- All continuation credits are transported through one shared shift. -/
theorem expectation (ws : List ℕ) (count : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ xs, F xs ∂law ws count =
      (∑ t ∈ Finset.range ws.sum, F (select count ws.sum t ws 0 0)) / ws.sum := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law]

/-- The marginal inclusion probability is `count * weight / total`. -/
theorem inclusion_probability (ws : List ℕ) (count i : ℕ) (hi : i < ws.length)
    (ht : 0 < ws.sum) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum) :
    law ws count {xs | (i : ℤ) ∈ xs} = (count * ws[i] : ℕ) / (ws.sum : ℝ≥0∞) := by
  rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet)]
  have hindicator : Set.indicator {xs : List ℤ | (i : ℤ) ∈ xs} (1 : List ℤ → ℝ≥0∞) =
      fun xs => if (i : ℤ) ∈ xs then 1 else 0 := by
    funext xs
    simp [Set.indicator_apply]
  rw [hindicator, expectation]
  congr 1
  exact_mod_cast inclusion_count ws count i hi ht hcap

end

end SampLib.SystematicPPS
