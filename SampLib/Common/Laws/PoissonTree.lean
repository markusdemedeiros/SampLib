module

public import SampLib.Common.Laws.PoissonLiveCount

@[expose] public section

/-! # The absorbing tree behind Duchon–Duvignau sampling

The live nodes are parity-constrained subsets. The three state coordinates record
their cardinality, ambient size, and largest omitted element. Starting from the empty
state, the stopping law is Poisson with mean one.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PoissonTree

noncomputable section

open Finset

structure State where
  count : ℕ
  size : ℕ
  boundary : ℕ
  deriving DecidableEq

def State.up (s : State) : State := ⟨s.count + 1, s.size + 1, s.boundary⟩

def State.down (s : State) : State := ⟨s.count - 1, s.size + 1, s.size + 1⟩

def node (a m b : ℕ) : State := ⟨a - m, a, b⟩

def layerSum (a : ℕ) (H : State → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
    (liveCount a m b : ℝ≥0∞) * H (node a m b)

def average (a : ℕ) (H : State → ℝ≥0∞) : ℝ≥0∞ := layerSum a H / a.factorial

def continuation (H : State → ℝ≥0∞) (s : State) : ℝ≥0∞ :=
  (H s.up + (s.size - s.boundary : ℕ) * H s.down) / (s.size + 1)

theorem layerSum_succ (a : ℕ) (H : State → ℝ≥0∞) :
    layerSum (a + 1) H =
      layerSum a (fun s => H s.up + (s.size - s.boundary : ℕ) * H s.down) := by
  simp only [layerSum]
  rw [live_sum_succ]
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ a := by have := mem_range.mp hm; omega
  apply sum_congr rfl
  intro b hb
  have hup : node (a + 1) m b = (node a m b).up := by
    dsimp only [node, State.up]
    congr 1
    omega
  have hdown : node (a + 1) (m + 2) (a + 1) = (node a m b).down := by
    dsimp only [node, State.down]
    congr 1
    omega
  rw [hup, hdown]
  rfl

theorem average_div_size (a : ℕ) (H : State → ℝ≥0∞) :
    average a (fun s => H s / (s.size + 1)) = layerSum a H / (a + 1).factorial := by
  have hc : layerSum a (fun s => H s / (s.size + 1)) =
      (a + 1 : ℝ≥0∞)⁻¹ * layerSum a H := by
    simp only [layerSum, node, ENNReal.div_eq_inv_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro b hb
    ring
  simp only [average]
  rw [hc, Nat.factorial_succ, Nat.cast_mul]
  simp only [ENNReal.div_eq_inv_mul, Nat.cast_add, Nat.cast_one]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  ring

theorem average_succ (a : ℕ) (H : State → ℝ≥0∞) :
    average (a + 1) H = average a (continuation H) := by
  unfold continuation
  rw [average_div_size, average, layerSum_succ]

@[simp] theorem average_zero (H : State → ℝ≥0∞) : average 0 H = H ⟨0, 0, 0⟩ := by
  simp [average, layerSum, liveCount, node]

/-- Unnormalized mass of outputs that stop after exactly `n` further live edges. -/
def layer : ℕ → State → Measure ℕ
  | 0, s => ((s.boundary : ℝ≥0∞) / (s.size + 1)) • Measure.dirac s.count
  | n + 1, s => ((1 : ℝ≥0∞) / (s.size + 1)) • layer n s.up +
      (((s.size - s.boundary : ℕ) : ℝ≥0∞) / (s.size + 1)) • layer n s.down

/-- The absorption measure, before its Poisson identification at the initial node. -/
def law (s : State) : Measure ℕ := Measure.sum (fun n => layer n s)

def credit (s : State) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law s

theorem layer_expectation_succ (n : ℕ) (s : State) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂layer (n + 1) s) =
      continuation (fun t => ∫⁻ k, F k ∂layer n t) s := by
  simp only [layer, continuation, lintegral_add_measure, lintegral_smul_measure,
    smul_eq_mul, ENNReal.div_eq_inv_mul]
  ring

/-- Forward counting of live nodes agrees with backward integration down the tree. -/
theorem average_layer (a n : ℕ) (F : ℕ → ℝ≥0∞) :
    average a (fun s => ∫⁻ k, F k ∂layer n s) =
      average (a + n) (fun s => ∫⁻ k, F k ∂layer 0 s) := by
  induction n generalizing a with
  | zero => simp
  | succ n IH =>
    simp_rw [layer_expectation_succ]
    rw [← average_succ, IH]
    congr 1
    omega

theorem initial_layer_expectation (n : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂layer n ⟨0, 0, 0⟩) =
      average n (fun s => (s.boundary : ℝ≥0∞) / (s.size + 1) * F s.count) := by
  have h := average_layer 0 n F
  simpa only [average_zero, Nat.zero_add, layer, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul] using h

theorem average_atom (a r : ℕ) :
    average a (fun s => if s.count = r then
      (s.boundary : ℝ≥0∞) / (s.size + 1) else 0) =
      if r ≤ a ∧ Even (a - r) then (a - r : ℕ) /
        ((r.factorial * (a - r + 1).factorial : ℕ) : ℝ≥0∞) else 0 := by
  have hdiv : (fun s : State => if s.count = r then
      (s.boundary : ℝ≥0∞) / (s.size + 1) else 0) =
      (fun s => (if s.count = r then (s.boundary : ℝ≥0∞) else 0) / (s.size + 1)) := by
    funext s
    split_ifs <;> simp
  rw [hdiv, average_div_size]
  by_cases hr : r ≤ a
  · have hnum : layerSum a (fun s => if s.count = r then (s.boundary : ℝ≥0∞) else 0) =
        ((∑ b ∈ range (a + 1), b * liveCount a (a - r) b : ℕ) : ℝ≥0∞) := by
      unfold layerSum
      rw [sum_eq_single_of_mem (a - r) (by simp only [mem_range]; omega)]
      · have hsub : a - (a - r) = r := by omega
        simp only [node, hsub, ite_true, Nat.cast_sum, Nat.cast_mul]
        apply sum_congr rfl
        intro b hb
        ring
      · intro m hm hne
        have hcount : a - m ≠ r := by have := mem_range.mp hm; omega
        simp [node, hcount]
    rw [hnum, sum_stopping_edges]
    by_cases he : Even (a - r)
    · rw [ite_eq_left ⟨he, Nat.sub_le a r⟩,
        normalized_stopping_edges a (a - r) (Nat.sub_le a r)]
      simp [hr, he, show a - (a - r) = r by omega]
    · simp [hr, he]
  · have hnum : layerSum a (fun s => if s.count = r then (s.boundary : ℝ≥0∞) else 0) =
        0 := by
      unfold layerSum
      apply sum_eq_zero
      intro m hm
      have hcount : a - m ≠ r := by omega
      simp [node, hcount]
    rw [hnum]
    simp [hr]

/-- At size `a`, the returned cardinality `r` leaves an even-sized complement. -/
theorem initial_layer_singleton (a r : ℕ) :
    layer a ⟨0, 0, 0⟩ {r} =
      if r ≤ a ∧ Even (a - r) then (a - r : ℕ) /
        ((r.factorial * (a - r + 1).factorial : ℕ) : ℝ≥0∞) else 0 := by
  have h := initial_layer_expectation a (({r} : Set ℕ).indicator (fun _ => 1))
  rw [lintegral_indicator (measurableSet_singleton r)] at h
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, one_mul] at h
  simp only [Set.indicator_apply, Set.mem_singleton_iff, mul_ite, mul_one, mul_zero] at h
  exact h.trans (average_atom a r)

/-- The absorbing tree has the standard unit-rate Poisson law. -/
theorem law_empty : law ⟨0, 0, 0⟩ = ProbabilityTheory.poissonMeasure 1 := by
  apply Measure.ext_of_singleton
  intro r
  rw [law, Measure.sum_apply _ (measurableSet_singleton r)]
  simp_rw [initial_layer_singleton]
  have hinj : Function.Injective (fun k : ℕ => r + 2 * k) := by
    intro i j hij
    dsimp only at hij
    omega
  rw [← hinj.tsum_eq ?_]
  · calc
      _ = ∑' k : ℕ, ((2 * k : ℕ) : ℝ≥0∞) /
          ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ≥0∞) := by
        apply tsum_congr
        intro k
        simp only [Nat.add_sub_cancel_left]
        rw [ite_eq_left ⟨by omega, even_two_mul k⟩]
      _ = _ := tsum_stopping_mass r
  · intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    have hcond : r ≤ a ∧ Even (a - r) := by
      by_contra hc
      simp [hc] at ha
    obtain ⟨k, hk⟩ := hcond.2
    exact ⟨k, by change r + 2 * k = a; omega⟩

/-- Partition absorbing paths by their first edge. -/
theorem credit_recurrence (s : State) (F : ℕ → ℝ≥0∞) :
    credit s F = (s.boundary : ℝ≥0∞) / (s.size + 1) * F s.count +
      (1 / (s.size + 1)) * credit s.up F +
      ((s.size - s.boundary : ℕ) : ℝ≥0∞) / (s.size + 1) * credit s.down F := by
  simp only [credit, law, lintegral_sum_measure]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [layer, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [add_assoc]

theorem initial_credit (F : ℕ → ℝ≥0∞) :
    credit ⟨1, 1, 0⟩ F = ∫⁻ k, F k ∂ProbabilityTheory.poissonMeasure 1 := by
  have h := credit_recurrence (⟨0, 0, 0⟩ : State) F
  have heq : credit ⟨0, 0, 0⟩ F = credit ⟨1, 1, 0⟩ F := by
    simpa [State.up] using h
  rw [← heq, credit, law_empty]

end

end SampLib.PoissonTree
