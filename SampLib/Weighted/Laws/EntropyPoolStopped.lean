import SampLib.Weighted.Laws.EntropyPool
import SampLib.Common.Laws.BitRecycler

/-! # Stopped credit of an entropy pool

The stopped functional pays accepted output credit before a fixed number of fresh
bits. It is additive, homogeneous, and monotone in the credit and in the horizon.
-/

open Finset MeasureTheory Filter
open scoped ENNReal Topology

namespace SampLib.EntropyPool

noncomputable section

/-- Accepted output credit before the indicated number of fresh bits; unresolved leaves pay zero. -/
def stopped (n : ℕ) : ℕ → ℕ → ℕ → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | 0, _, _, _ => 0
  | T + 1, width, value, F =>
    (∑ b ∈ range 2, BitRecycler.kernel .lower n F
      (fun w v => stopped n T w v F) (width * 2) (value * 2 + b)) / 2

private theorem kernel_add (n width value : ℕ) (F G : ℕ → ℝ≥0∞)
    (A B : ℕ → ℕ → ℝ≥0∞) :
    BitRecycler.kernel .lower n (fun r => F r + G r)
      (fun w v => A w v + B w v) width value =
      BitRecycler.kernel .lower n F A width value +
        BitRecycler.kernel .lower n G B width value := by
  by_cases hw : n ≤ width <;> by_cases hv : value < n <;>
    simp [BitRecycler.kernel, hw, hv]

/-- A finite execution pays its accepted leaves and one unit on every unresolved leaf. -/
theorem credit_eq_stopped_add_tail (n T width value : ℕ) (F : ℕ → ℝ≥0∞) :
    BitRecycler.credit .lower n F T width value = stopped n T width value F +
      BitRecycler.credit .lower n (fun _ => 0) T width value := by
  induction T generalizing width value with
  | zero => simp [stopped, BitRecycler.credit]
  | succ T IH =>
    have hnext : BitRecycler.credit .lower n F T =
        fun w v => stopped n T w v F + BitRecycler.credit .lower n (fun _ => 0) T w v := by
      funext w v
      exact IH w v
    simp only [BitRecycler.credit, stopped]
    rw [hnext]
    have hkernel (b : ℕ) := kernel_add n (width * 2) (value * 2 + b) F (fun _ => 0)
      (fun w v => stopped n T w v F) (BitRecycler.credit .lower n (fun _ => 0) T)
    simp only [add_zero] at hkernel
    simp_rw [hkernel]
    simp [sum_add_distrib, ENNReal.div_eq_inv_mul, mul_add]

/-- The recycler kernel is monotone in the output and continuation credits. -/
theorem kernel_mono (n width value : ℕ) (F G : ℕ → ℝ≥0∞)
    (A B : ℕ → ℕ → ℝ≥0∞) (hF : ∀ r, F r ≤ G r) (hA : ∀ w v, A w v ≤ B w v) :
    BitRecycler.kernel .lower n F A width value ≤ BitRecycler.kernel .lower n G B width value := by
  by_cases hw : n ≤ width
  · by_cases hv : value < n
    · simpa [BitRecycler.kernel, hw, hv] using hF value
    · simpa [BitRecycler.kernel, hw, hv] using hA (width - n) (value - n)
  · simpa [BitRecycler.kernel, hw] using hA width value

private theorem kernel_mul (n width value : ℕ) (F : ℕ → ℝ≥0∞)
    (A : ℕ → ℕ → ℝ≥0∞) (c : ℝ≥0∞) :
    BitRecycler.kernel .lower n (fun r => F r * c) (fun w v => A w v * c) width value =
      BitRecycler.kernel .lower n F A width value * c := by
  by_cases hw : n ≤ width <;> by_cases hv : value < n <;>
    simp [BitRecycler.kernel, hw, hv]

theorem stopped_zero (n T width value : ℕ) : stopped n T width value (fun _ => 0) = 0 := by
  induction T generalizing width value with
  | zero => rfl
  | succ T IH => simp [stopped, BitRecycler.kernel, IH]

theorem stopped_add (n T width value : ℕ) (F G : ℕ → ℝ≥0∞) :
    stopped n T width value (fun r => F r + G r) =
      stopped n T width value F + stopped n T width value G := by
  induction T generalizing width value with
  | zero => simp [stopped]
  | succ T IH =>
    have hnext : (fun w v => stopped n T w v (fun r => F r + G r)) =
        fun w v => stopped n T w v F + stopped n T w v G := by
      funext w v
      exact IH w v
    simp only [stopped, hnext, kernel_add]
    simp [sum_add_distrib, ENNReal.div_eq_inv_mul, mul_add]

theorem stopped_mul (n T width value : ℕ) (F : ℕ → ℝ≥0∞) (c : ℝ≥0∞) :
    stopped n T width value (fun r => F r * c) = stopped n T width value F * c := by
  induction T generalizing width value with
  | zero => simp [stopped]
  | succ T IH =>
    have hnext : (fun w v => stopped n T w v (fun r => F r * c)) =
        fun w v => stopped n T w v F * c := by
      funext w v
      exact IH w v
    simp only [stopped, hnext, kernel_mul]
    rw [← sum_mul]
    simp only [ENNReal.div_eq_inv_mul]
    ring

theorem stopped_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞)
    (n T width value : ℕ) :
    stopped n T width value (fun r => ∑ i ∈ s, f i r) =
      ∑ i ∈ s, stopped n T width value (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stopped_zero]
  | @insert i s hi IH => simp [sum_insert, hi, stopped_add, IH]

theorem stopped_mono (n T width value : ℕ) (F G : ℕ → ℝ≥0∞) (hF : ∀ r, F r ≤ G r) :
    stopped n T width value F ≤ stopped n T width value G := by
  induction T generalizing width value with
  | zero => rfl
  | succ T IH =>
    unfold stopped
    apply ENNReal.div_le_div_right _ 2
    exact sum_le_sum fun b _ => kernel_mono _ _ _ _ _ _ _ hF IH

/-- Accepted finite-leaf credit increases as the bit horizon grows. -/
theorem stopped_mono_time (n width value : ℕ) (F : ℕ → ℝ≥0∞) :
    Monotone (fun T => stopped n T width value F) := by
  apply monotone_nat_of_le_succ
  intro T
  induction T generalizing width value with
  | zero => simp [stopped]
  | succ T IH =>
    unfold stopped
    apply ENNReal.div_le_div_right _ 2
    exact sum_le_sum fun b _ => kernel_mono _ _ _ _ _ _ _ (fun _ => le_rfl) IH

theorem credit_one (n T width value : ℕ) :
    BitRecycler.credit .lower n (fun _ => 1) T width value = 1 := by
  induction T generalizing width value with
  | zero => rfl
  | succ T IH =>
    simp [BitRecycler.credit, BitRecycler.kernel, IH]
    exact ENNReal.div_self (by norm_num) (by finiteness)

/-- Accepted and unresolved finite-leaf masses sum to one. -/
theorem stopped_one_add_tail (n T width value : ℕ) :
    stopped n T width value (fun _ => 1) +
      BitRecycler.credit .lower n (fun _ => 0) T width value = 1 := by
  rw [← credit_eq_stopped_add_tail, credit_one]

theorem stopped_one_le (n T width value : ℕ) : stopped n T width value (fun _ => 1) ≤ 1 := by
  calc
    _ ≤ stopped n T width value (fun _ => 1) +
        BitRecycler.credit .lower n (fun _ => 0) T width value := le_add_right le_rfl
    _ = 1 := stopped_one_add_tail n T width value

private theorem kernel_congr (n width value : ℕ) (F G : ℕ → ℝ≥0∞)
    (A B : ℕ → ℕ → ℝ≥0∞) (hF : ∀ r, r < n → F r = G r)
    (hA : ∀ w v, A w v = B w v) :
    BitRecycler.kernel .lower n F A width value = BitRecycler.kernel .lower n G B width value := by
  by_cases hw : n ≤ width
  · by_cases hv : value < n
    · simpa [BitRecycler.kernel, hw, hv] using hF value hv
    · simpa [BitRecycler.kernel, hw, hv] using hA (width - n) (value - n)
  · simpa [BitRecycler.kernel, hw] using hA width value

theorem stopped_congr (n T width value : ℕ) (F G : ℕ → ℝ≥0∞)
    (hF : ∀ r, r < n → F r = G r) : stopped n T width value F = stopped n T width value G := by
  induction T generalizing width value with
  | zero => rfl
  | succ T IH =>
    unfold stopped
    congr 1
    apply sum_congr rfl
    intro b _
    exact kernel_congr _ _ _ _ _ _ _ hF IH

end

end SampLib.EntropyPool
