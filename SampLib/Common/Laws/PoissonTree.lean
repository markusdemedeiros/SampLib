module

public import SampLib.Common.Laws.PoissonMeasure
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

/-! # The absorbing tree behind Duchon–Duvignau sampling

The live nodes are parity-constrained subsets. The three state coordinates record
their cardinality, ambient size, and largest omitted element.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PoissonTree

noncomputable section

open Finset

/-- Hockey-stick summation, including indices below the lower argument. -/
theorem sum_choose (n k : ℕ) :
    ∑ i ∈ range n, i.choose k = n.choose (k + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ, IH, Nat.choose_succ_succ']
    exact Nat.add_comm _ _

/-- Sum the possible largest omitted labels in an `m`-element complement. -/
theorem sum_largest_label (n m : ℕ) (hm : 0 < m) :
    ∑ i ∈ range n, (i + 1) * i.choose (m - 1) =
      m * (n + 1).choose (m + 1) := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simp_rw [Nat.add_one_mul_choose_eq, hm', mul_comm _ m]
  rw [← mul_sum]
  congr 1
  have h := sum_choose (n + 1) m
  rw [sum_range_succ'] at h
  simpa [Nat.choose_eq_zero_of_lt hm] using h

/-- A second hockey-stick sum counts predecessors whose last omitted label increases. -/
theorem sum_live_predecessors (n m : ℕ) (hm : 0 < m) :
    ∑ i ∈ range n, (n - (i + 1)) * i.choose (m - 1) = n.choose (m + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ]
    simp only [Nat.add_sub_add_right, Nat.sub_self, zero_mul, add_zero]
    have hsplit : (∑ i ∈ range n, (n - i) * i.choose (m - 1)) =
        (∑ i ∈ range n, (n - (i + 1)) * i.choose (m - 1)) +
          ∑ i ∈ range n, i.choose (m - 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      have hsub : n - i = n - (i + 1) + 1 := by have := mem_range.mp hi; omega
      rw [hsub, add_mul, one_mul]
    rw [hsplit, IH, sum_choose, Nat.sub_add_cancel hm, Nat.choose_succ_succ']
    exact Nat.add_comm _ _

/-- The parity-subset stopping weights are the difference of the even and odd
exponential series. -/
theorem hasSum_stopping_weights :
    HasSum (fun k : ℕ => ((2 * k : ℕ) : ℝ) / (2 * k + 1).factorial)
      (Real.exp (-1)) := by
  have h := (Real.hasSum_cosh (1 : ℝ)).sub (Real.hasSum_sinh (1 : ℝ))
  simp only [one_pow, Real.cosh_sub_sinh] at h
  convert h using 1
  ext k
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- After fixing the returned cardinality, the stopping weights have Poisson mass. -/
theorem hasSum_stopping_mass (r : ℕ) :
    HasSum (fun k : ℕ => ((2 * k : ℕ) : ℝ) /
      ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ))
      (Real.exp (-1) / r.factorial) := by
  convert hasSum_stopping_weights.div_const (r.factorial : ℝ) using 1
  ext k
  rw [div_div]
  push_cast
  congr 1
  ring

theorem tsum_stopping_mass (r : ℕ) :
    (∑' k : ℕ, ((2 * k : ℕ) : ℝ≥0∞) /
      ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ≥0∞)) =
      ProbabilityTheory.poissonMeasure 1 {r} := by
  rw [ProbabilityTheory.poissonMeasure_singleton]
  simp only [NNReal.coe_one, one_pow, mul_one]
  have h := hasSum_stopping_mass r
  calc
    _ = ∑' k : ℕ, ENNReal.ofReal (((2 * k : ℕ) : ℝ) /
        ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ)) := by
      apply tsum_congr
      intro k
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑' k : ℕ, ((2 * k : ℕ) : ℝ) /
        ((r.factorial * (2 * k + 1).factorial : ℕ) : ℝ)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h.summable).symm
    _ = _ := by rw [h.tsum_eq]

/-- Live paths indexed by the number of omitted labels and their largest label. -/
def liveCount (a m b : ℕ) : ℕ :=
  if m = 0 then if b = 0 then 1 else 0
  else if Even m ∧ m ≤ a ∧ b ≠ 0 ∧ b ≤ a then (b - 1).choose (m - 1) else 0

@[simp] theorem liveCount_zero_omitted (a b : ℕ) :
    liveCount a 0 b = if b = 0 then 1 else 0 := by simp [liveCount]

@[simp] theorem liveCount_zero_boundary (a m : ℕ) :
    liveCount a m 0 = if m = 0 then 1 else 0 := by simp [liveCount]

theorem liveCount_up (a m b : ℕ) (hb : b ≤ a) :
    liveCount (a + 1) m b = liveCount a m b := by
  by_cases hm : m = 0
  · simp [liveCount, hm]
  by_cases hb0 : b = 0
  · simp [liveCount, hm, hb0]
  by_cases he : Even m
  · by_cases hma : m ≤ a
    · simp [liveCount, hm, hb0, he, hma, hb, show m ≤ a + 1 by omega,
        show b ≤ a + 1 by omega]
    · have hz : (b - 1).choose (m - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [liveCount, hm, hb0, he, hma, hz]
  · simp [liveCount, hm, he]

theorem liveCount_down (a m : ℕ) :
    liveCount (a + 1) (m + 2) (a + 1) =
      ∑ b ∈ range (a + 1), (a - b) * liveCount a m b := by
  have heq : Even (m + 2) ↔ Even m := by simp [Nat.even_add]
  by_cases he : Even m
  · have hleft : liveCount (a + 1) (m + 2) (a + 1) = a.choose (m + 1) := by
      have he' := heq.mpr he
      by_cases hma : m + 2 ≤ a + 1
      · simp [liveCount, he', hma]
      · have hz : a.choose (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [liveCount, he', hma, hz]
    rw [hleft]
    by_cases hm : m = 0
    · subst m
      rw [sum_range_succ']
      simp
    by_cases hma : m ≤ a
    · rw [sum_range_succ']
      simp only [liveCount_zero_boundary, hm, ite_false, mul_zero, add_zero]
      rw [show (∑ i ∈ range a, (a - (i + 1)) * liveCount a m (i + 1)) =
          ∑ i ∈ range a, (a - (i + 1)) * i.choose (m - 1) by
        apply sum_congr rfl
        intro i hi
        simp [liveCount, hm, he, hma, show i + 1 ≤ a by have := mem_range.mp hi; omega]]
      exact (sum_live_predecessors a m (by omega)).symm
    · have hz : a.choose (m + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [liveCount, hm, he, hma, hz]
  · have he' : ¬Even (m + 2) := fun h => he (heq.mp h)
    have hm : m ≠ 0 := by intro h; subst m; simp at he
    simp [liveCount, he, he', hm]

theorem liveCount_support {a m b : ℕ} (h : liveCount a m b ≠ 0) :
    m ≤ a ∧ m ≤ b ∧ b ≤ a := by
  by_cases hm : m = 0
  · subst m
    have hb : b = 0 := by
      by_contra hb
      simp [liveCount, hb] at h
    subst b
    omega
  · by_cases hvalid : Even m ∧ m ≤ a ∧ b ≠ 0 ∧ b ≤ a
    · have hc : (b - 1).choose (m - 1) ≠ 0 := by simpa [liveCount, hm, hvalid] using h
      have hmb := Nat.choose_ne_zero_iff.mp hc
      exact ⟨hvalid.2.1, by omega, hvalid.2.2.2⟩
    · simp [liveCount, hm, hvalid] at h

theorem liveCount_above_size (a m b : ℕ) (h : a < m) : liveCount a m b = 0 := by
  by_contra hc
  have := (liveCount_support hc).1
  omega

theorem liveCount_diagonal (a b : ℕ) : (a - b) * liveCount a a b = 0 := by
  by_cases h : liveCount a a b = 0
  · rw [h, mul_zero]
  · have hb := (liveCount_support h).2.1
    simp [Nat.sub_eq_zero_of_le hb]

/-- Splitting a live layer into its fixed-point and deletion children. -/
theorem live_sum_succ (a : ℕ) (G : ℕ → ℕ → ℝ≥0∞) :
    (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 2),
      (liveCount (a + 1) m b : ℝ≥0∞) * G m b) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * (G m b + (a - b : ℕ) * G (m + 2) (a + 1)) := by
  have hup : (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 1),
      (liveCount (a + 1) m b : ℝ≥0∞) * G m b) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * G m b := by
    rw [show a + 2 = (a + 1) + 1 by omega, sum_range_succ]
    have hlast : (∑ b ∈ range (a + 1),
        (liveCount (a + 1) (a + 1) b : ℝ≥0∞) * G (a + 1) b) = 0 := by
      apply sum_eq_zero
      intro b hb
      rw [liveCount_up a (a + 1) b (by have := mem_range.mp hb; omega),
        liveCount_above_size a (a + 1) b (by omega)]
      simp
    rw [hlast, add_zero]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro b hb
    rw [liveCount_up a m b (by have := mem_range.mp hb; omega)]
  have hdown : (∑ m ∈ range (a + 2),
      (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1)) =
      ∑ m ∈ range (a + 1), ∑ b ∈ range (a + 1),
        (liveCount a m b : ℝ≥0∞) * (a - b : ℕ) * G (m + 2) (a + 1) := by
    have hzero : liveCount (a + 1) 0 (a + 1) = 0 := by simp
    have hone : liveCount (a + 1) 1 (a + 1) = 0 := by simp [liveCount]
    have hfirst : (∑ m ∈ range 2,
        (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1)) = 0 := by
      simp [sum_range_succ, hzero, hone]
    conv_lhs => rw [show a + 2 = 2 + a by omega, sum_range_add, hfirst, zero_add]
    rw [sum_range_succ]
    have hlast : (∑ b ∈ range (a + 1),
        (liveCount a a b : ℝ≥0∞) * (a - b : ℕ) * G (a + 2) (a + 1)) = 0 := by
      apply sum_eq_zero
      intro b hb
      have h := liveCount_diagonal a b
      have hc : (liveCount a a b : ℝ≥0∞) * (a - b : ℕ) = 0 := by
        exact_mod_cast (by simpa [Nat.mul_comm] using h)
      rw [hc, zero_mul]
    rw [hlast, add_zero]
    apply sum_congr rfl
    intro m hm
    rw [show 2 + m = m + 2 by omega, liveCount_down, Nat.cast_sum, sum_mul]
    apply sum_congr rfl
    intro b hb
    simp only [Nat.cast_mul]
    ring
  calc
    _ = (∑ m ∈ range (a + 2), ∑ b ∈ range (a + 1),
        (liveCount (a + 1) m b : ℝ≥0∞) * G m b) +
        ∑ m ∈ range (a + 2),
          (liveCount (a + 1) m (a + 1) : ℝ≥0∞) * G m (a + 1) := by
      conv_lhs => arg 2; ext m; rw [sum_range_succ]
      rw [sum_add_distrib]
    _ = _ := by
      rw [hup, hdown]
      simp only [mul_add, sum_add_distrib, mul_assoc]

/-- Count the stopping edges of a fixed-cardinality parity layer. -/
theorem sum_stopping_edges (a m : ℕ) :
    ∑ b ∈ range (a + 1), b * liveCount a m b =
      if Even m ∧ m ≤ a then m * (a + 1).choose (m + 1) else 0 := by
  by_cases hm : m = 0
  · subst m
    rw [sum_range_succ']
    simp
  by_cases he : Even m
  · by_cases hma : m ≤ a
    · rw [ite_eq_left ⟨he, hma⟩, sum_range_succ']
      simp only [zero_mul, add_zero]
      rw [show (∑ i ∈ range a, (i + 1) * liveCount a m (i + 1)) =
          ∑ i ∈ range a, (i + 1) * i.choose (m - 1) by
        apply sum_congr rfl
        intro i hi
        simp [liveCount, hm, he, hma, show i + 1 ≤ a by have := mem_range.mp hi; omega]]
      exact sum_largest_label a m (by omega)
    · simp [liveCount, hm, he, hma]
  · simp [liveCount, hm, he]

/-- Factorial normalization leaves the Poisson coefficient at each stopping layer. -/
theorem normalized_stopping_edges (a m : ℕ) (hm : m ≤ a) :
    ((m * (a + 1).choose (m + 1) : ℕ) : ℝ≥0∞) / (a + 1).factorial =
      (m : ℝ≥0∞) / (((a - m).factorial * (m + 1).factorial : ℕ) : ℝ≥0∞) := by
  have hf : (a + 1).factorial =
      (a + 1).choose (m + 1) * (m + 1).factorial * (a - m).factorial := by
    simpa only [Nat.add_sub_add_right] using
      (Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ a + 1 by omega)).symm
  have hc : ((a + 1).choose (m + 1) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show m + 1 ≤ a + 1 by omega)).ne'
  rw [hf]
  simp only [Nat.cast_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ENNReal.mul_div_mul_left (m : ℝ≥0∞)
      (((m + 1).factorial : ℝ≥0∞) * (a - m).factorial) hc (by simp)

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

/-- The live-edge potential contracts after size two, even when the boundary is zero. -/
theorem potential_bound (a b : ℕ) (ha : 2 ≤ a) :
    (3 : ℝ) * (a - b + 1 : ℕ) / (a + 1) ≤ (a - b + 1 : ℕ) := by
  have hpos : (0 : ℝ) < a + 1 := by positivity
  rw [div_le_iff₀ hpos]
  have ha' : (3 : ℝ) ≤ a + 1 := by exact_mod_cast (show 3 ≤ a + 1 by omega)
  simpa [mul_comm] using mul_le_mul_of_nonneg_right ha' (by positivity :
    (0 : ℝ) ≤ (a - b + 1 : ℕ))

end

end SampLib.PoissonTree
