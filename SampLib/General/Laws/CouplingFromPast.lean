import SampLib.General.Laws.IIDList

/-! # Coupling from the past on a finite random-mapping representation

A stationary input remains stationary after any independent older block. Once
that block coalesces, its image is a single exact stationary sample. A positive
finite coalescent block gives a bounded remaining-round potential for doubling.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.CouplingFromPast

noncomputable section

abbrev Map (n : ℕ) := Fin n → Fin n

def applyMaps {n : ℕ} (maps : List (Map n)) (x : Fin n) : Fin n :=
  maps.foldl (fun y f => f y) x

@[simp] theorem applyMaps_nil {n : ℕ} (x : Fin n) : applyMaps [] x = x := rfl

@[simp] theorem applyMaps_cons {n : ℕ} (f : Map n) (fs : List (Map n)) (x : Fin n) :
    applyMaps (f :: fs) x = applyMaps fs (f x) := rfl

@[simp] theorem applyMaps_append {n : ℕ} (older newer : List (Map n)) (x : Fin n) :
    applyMaps (older ++ newer) x = applyMaps newer (applyMaps older x) := by
  exact List.foldl_append

/-- Every starting state has the same image under the stored chronological maps. -/
abbrev Coalesces {n : ℕ} (maps : List (Map n)) : Prop :=
  ∀ x y, applyMaps maps x = applyMaps maps y

theorem coalesces_append {n : ℕ} {older : List (Map n)} (h : Coalesces older)
    (newer : List (Map n)) : Coalesces (older ++ newer) := by
  intro x y
  simp only [applyMaps_append, h x y]

theorem coalesces_of_take {n : ℕ} {older : List (Map n)} (L : ℕ)
    (h : Coalesces (older.take L)) (newer : List (Map n)) : Coalesces (older ++ newer) := by
  have hc := coalesces_append h (older.drop L ++ newer)
  simpa only [← List.append_assoc, List.take_append_drop] using hc

/-- The Markov kernel induced by one random mapping. -/
def transition {n : ℕ} (ρ : Measure (Map n)) (x : Fin n) : Measure (Fin n) :=
  ρ.map (fun f => f x)

/-- Stationarity concerns the single-map induced kernel, without positivity assumptions. -/
def Stationary {n : ℕ} (ρ : Measure (Map n)) (π : Measure (Fin n)) : Prop :=
  π.bind (transition ρ) = π

/-- The remaining target credit for a fixed newer history. -/
def credit {n : ℕ} (π : Measure (Fin n)) (maps : List (Map n))
    (F : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, F (applyMaps maps x) ∂π

@[simp] theorem credit_nil {n : ℕ} (π : Measure (Fin n)) (F : Fin n → ℝ≥0∞) :
    credit π [] F = ∫⁻ x, F x ∂π := rfl

/-- A coalescent history turns its stationary expectation into the returned credit. -/
theorem credit_coalesces {n : ℕ} (π : Measure (Fin n)) [IsProbabilityMeasure π]
    (maps : List (Map n)) (h : Coalesces maps) (x : Fin n) (F : Fin n → ℝ≥0∞) :
    credit π maps F = F (applyMaps maps x) := by
  unfold credit
  simp_rw [h _ x]
  simp

theorem prepend_expectation {n : ℕ} (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n)) (hπ : Stationary ρ π) (newer : List (Map n))
    (F : Fin n → ℝ≥0∞) :
    ∫⁻ f, credit π (f :: newer) F ∂ρ = credit π newer F := by
  unfold credit
  simp only [applyMaps_cons]
  rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
  conv_rhs =>
    rw [← hπ, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  simp only [transition, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Prepending any iid older block preserves stationary continuation credit. -/
theorem block_expectation {n : ℕ} (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n)) (hπ : Stationary ρ π) (h : ℕ) (newer : List (Map n))
    (F : Fin n → ℝ≥0∞) :
    ∫⁻ older, credit π (older ++ newer) F ∂IIDList.law ρ h = credit π newer F := by
  induction h with
  | zero => simp [IIDList.law]
  | succ h IH =>
    rw [← IIDList.expectation]
    simp only [List.cons_append]
    rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
    simp_rw [prepend_expectation ρ π hπ]
    exact IH

/-- A positive lower bound for the probability of a finite coalescent block. -/
structure Block {n : ℕ} (ρ : Measure (Map n)) where
  length : ℕ
  chance : ℝ≥0
  positive : 0 < chance
  bound : (chance : ℝ≥0∞) ≤ (IIDList.law ρ length) {maps | Coalesces maps}

namespace Block

variable {n : ℕ} {ρ : Measure (Map n)} [IsProbabilityMeasure ρ]

theorem chance_le_one (b : Block ρ) : b.chance ≤ 1 := by
  have h := b.bound.trans (prob_le_one)
  exact_mod_cast h

/-- This data is available for every finite coalescent block of positive probability. -/
theorem exists_iff : Nonempty (Block ρ) ↔
    ∃ L, 0 < (IIDList.law ρ L) {maps | Coalesces maps} := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.length, (ENNReal.coe_pos.mpr b.positive).trans_le b.bound⟩
  · rintro ⟨L, hL⟩
    have hfin : (IIDList.law ρ L) {maps | Coalesces maps} ≠ ∞ := measure_ne_top _ _
    refine ⟨⟨L, ((IIDList.law ρ L) {maps | Coalesces maps}).toNNReal, ?_, ?_⟩⟩
    · exact ENNReal.toNNReal_pos hL.ne' hfin
    · rw [ENNReal.coe_toNNReal hfin]

theorem failure_bound (b : Block ρ) (h : ℕ) (hh : b.length ≤ h)
    (newer : List (Map n)) :
    (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} ≤ 1 - (b.chance : ℝ≥0∞) := by
  have hsub : {older : List (Map n) | ¬Coalesces (older ++ newer)} ⊆
      (List.take b.length) ⁻¹' {segment | ¬Coalesces segment} := by
    intro older hbad hgood
    exact hbad (coalesces_of_take b.length hgood newer)
  calc
    _ ≤ (IIDList.law ρ h) ((List.take b.length) ⁻¹' {segment | ¬Coalesces segment}) :=
      measure_mono hsub
    _ = (IIDList.law ρ b.length) {segment | ¬Coalesces segment} := by
      rw [← IIDList.take_map ρ b.length h hh,
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    _ ≤ _ := by
      rw [show {segment : List (Map n) | ¬Coalesces segment} = {segment | Coalesces segment}ᶜ
        from rfl, measure_compl (Set.to_countable _).measurableSet (measure_ne_top _ _),
        measure_univ]
      exact tsub_le_tsub_left b.bound 1

end Block

end

end SampLib.CouplingFromPast
