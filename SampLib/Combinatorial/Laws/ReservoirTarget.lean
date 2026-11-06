module

public import SampLib.Combinatorial.Laws.ReservoirProcess
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! # The closed-form law of Algorithm R

A selected initial item remains in its original slot. Conditional on the selected
subset, the selected later items occupy the remaining slots uniformly. Thus an
admissible tuple with m later items has mass 1 / (choose(n,k) * m!). One reservoir step
draws a uniform ticket.
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

end

end SampLib.ReservoirLaw
