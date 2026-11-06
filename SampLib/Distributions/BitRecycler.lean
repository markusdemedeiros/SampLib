import SampLib.Samplers.UniformInt

/-! # Finite-horizon credit for uniform bit recycling

Pairing each retained rank with one fair bit enumerates the doubled interval.
Removing either its lower or upper block of `n` ranks gives the same bulk credit
identity. The surviving interval has width below `n`, so its cutoff mass is at
most `(n-1)/2^T`. No individual state is assumed to have a uniform output law.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace SampLib.BitRecycler

noncomputable section

inductive Orientation where
  | lower
  | upper
  deriving DecidableEq

theorem expanded_lt (v c b : ℕ) (hc : c < v) (hb : b < 2) : c * 2 + b < v * 2 := by
  omega

theorem residual_width_lt (n v : ℕ) (hv : v < n) : v * 2 - n < n := by omega

theorem lower_recycle_lt (n w x : ℕ) (hnx : n ≤ x) (hx : x < w) : x - n < w - n := by
  omega

theorem upper_output_lt (n w x : ℕ) (haccept : w - n ≤ x) (hx : x < w) :
    x - (w - n) < n := by omega

/-- The common one-bit kernel, after doubling the width and appending the bit. -/
def kernel (o : Orientation) (n : ℕ) (F : ℕ → ℝ≥0∞) (K : ℕ → ℕ → ℝ≥0∞)
    (w x : ℕ) : ℝ≥0∞ :=
  if n ≤ w then
    match o with
    | .lower => if x < n then F x else K (w - n) (x - n)
    | .upper => if w - n ≤ x then F (x - (w - n)) else K (w - n) x
  else K w x

/-- At the horizon, one credit makes the unexecuted suffix contradictory. -/
def credit (o : Orientation) (n : ℕ) (F : ℕ → ℝ≥0∞) : ℕ → ℕ → ℕ → ℝ≥0∞
  | 0, _, _ => 1
  | T + 1, v, c =>
    (∑ b ∈ range 2, kernel o n F (credit o n F T) (v * 2) (c * 2 + b)) / 2

def bitCredit (o : Orientation) (n T : ℕ) (F : ℕ → ℝ≥0∞) (v c b : ℕ) : ℝ≥0∞ :=
  kernel o n F (credit o n F T) (v * 2) (c * 2 + b)

@[simp] theorem credit_zero (o : Orientation) (n v c : ℕ) (F : ℕ → ℝ≥0∞) :
    credit o n F 0 v c = 1 := rfl

/-- One fair bit pays its conditional continuation credit exactly. -/
theorem expectation (o : Orientation) (n T : ℕ) (F : ℕ → ℝ≥0∞) (v c : ℕ) :
    (∑ b ∈ range 2, bitCredit o n T F v c b) / 2 = credit o n F (T + 1) v c := rfl

/-- Expected continuation credit under the independently specified uniform law. -/
def outputCredit (n : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := (∑ j ∈ range n, F j) / n

private theorem output_sum (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    (∑ j ∈ range n, F j) = (n : ℝ≥0∞) * outputCredit n F := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [outputCredit, mul_comm] using
    (ENNReal.div_mul_cancel hn0 (by finiteness) (b := ∑ j ∈ range n, F j)).symm

private theorem sum_bits {α : Type _} [AddCommMonoid α] (f : ℕ → α) (v : ℕ) :
    (∑ c ∈ range v, ∑ b ∈ range 2, f (c * 2 + b)) = ∑ x ∈ range (v * 2), f x := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [sum_range_succ, ih, Nat.add_mul, Nat.one_mul, sum_range_add]

/-- Either orientation emits each output once and leaves the same residual interval. -/
theorem kernel_sum (o : Orientation) (n w : ℕ) (hnw : n ≤ w)
    (F : ℕ → ℝ≥0∞) (K : ℕ → ℕ → ℝ≥0∞) :
    (∑ x ∈ range w, kernel o n F K w x) =
      (∑ j ∈ range n, F j) + ∑ c ∈ range (w - n), K (w - n) c := by
  cases o with
  | lower =>
    have hs := sum_range_add (fun x => kernel .lower n F K w x) n (w - n)
    rw [Nat.add_sub_of_le hnw] at hs
    rw [hs]
    congr 1
    · apply sum_congr rfl
      intro x hx
      simp only [kernel, ite_eq_left hnw, ite_eq_left (mem_range.mp hx)]
    · apply sum_congr rfl
      intro x hx
      simp only [kernel, ite_eq_left hnw, ite_eq_right (by omega : ¬n + x < n),
        Nat.add_sub_cancel_left]
  | upper =>
    have hs := sum_range_add (fun x => kernel .upper n F K w x) (w - n) n
    rw [Nat.sub_add_cancel hnw] at hs
    rw [hs, add_comm]
    congr 1
    · apply sum_congr rfl
      intro x hx
      simp only [kernel, ite_eq_left hnw, ite_eq_left (by omega : w - n ≤ w - n + x),
        Nat.add_sub_cancel_left]
    · apply sum_congr rfl
      intro x hx
      simp only [kernel, ite_eq_left hnw,
        ite_eq_right (not_le.mpr (mem_range.mp hx))]

private theorem sum_successor (o : Orientation) (n T v : ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ c ∈ range v, credit o n F (T + 1) v c) =
      (∑ x ∈ range (v * 2), kernel o n F (credit o n F T) (v * 2) x) / 2 := by
  simp only [credit, ENNReal.div_eq_inv_mul, mul_sum]
  rw [← sum_bits]

private theorem halve (v : ℕ) (A B : ℝ≥0∞) :
    (((v * 2 : ℕ) : ℝ≥0∞) * A + B) / 2 = (v : ℝ≥0∞) * A + B / 2 := by
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by finiteness)
  calc
    _ = ((2 : ℝ≥0∞)⁻¹ * 2) * ((v : ℝ≥0∞) * A) + B / 2 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ = _ := by rw [htwo, one_mul]

private theorem tail_halve (n T : ℕ) :
    ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T / 2 = ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ (T + 1) := by
  simp only [pow_succ, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inr (by norm_num))]
  ring

/-- Bulk credit follows interval cardinalities, with exponentially vanishing cutoff mass. -/
theorem sum_credit_le (o : Orientation) (n : ℕ) (hn : 0 < n) (T v : ℕ)
    (hv : v < n) (F : ℕ → ℝ≥0∞) :
    (∑ c ∈ range v, credit o n F T v c) ≤
      (v : ℝ≥0∞) * outputCredit n F + ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  induction T generalizing v with
  | zero =>
    have hvn : (v : ℝ≥0∞) ≤ (n - 1 : ℕ) := by exact_mod_cast (show v ≤ n - 1 by omega)
    simpa only [credit_zero, sum_const, card_range, nsmul_eq_mul, mul_one, pow_zero, div_one] using
      hvn.trans (le_add_left le_rfl)
  | succ T ih =>
    rw [sum_successor]
    by_cases hnw : n ≤ v * 2
    · have hr : v * 2 - n < n := by omega
      have hwidth : n + (v * 2 - n) = v * 2 := Nat.add_sub_of_le hnw
      rw [kernel_sum o n (v * 2) hnw F, output_sum n hn F]
      calc
        _ ≤ ((n : ℝ≥0∞) * outputCredit n F +
            ((v * 2 - n : ℕ) * outputCredit n F + (n - 1 : ℕ) / (2 : ℝ≥0∞) ^ T)) / 2 := by
          exact ENNReal.div_le_div_right (add_le_add le_rfl (ih _ hr)) 2
        _ = (((v * 2 : ℕ) : ℝ≥0∞) * outputCredit n F + (n - 1 : ℕ) / 2 ^ T) / 2 := by
          rw [← add_assoc, ← add_mul, ← Nat.cast_add, hwidth]
        _ = _ := by rw [halve, tail_halve]
    · have hw : v * 2 < n := lt_of_not_ge hnw
      simp only [kernel, ite_eq_right hnw]
      calc
        _ ≤ (((v * 2 : ℕ) : ℝ≥0∞) * outputCredit n F + (n - 1 : ℕ) / 2 ^ T) / 2 := by
          exact ENNReal.div_le_div_right (ih _ hw) 2
        _ = _ := by rw [halve, tail_halve]

/-- The initial width-one state needs only the uniform expectation and the cutoff tail. -/
theorem initial_bound (o : Orientation) (n : ℕ) (hn : 0 < n) (hOne : 1 < n)
    (T : ℕ) (F : ℕ → ℝ≥0∞) :
    credit o n F T 1 0 ≤ (∫⁻ j, F j ∂UniformInt.law n) +
      ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  simpa only [sum_range_one, Nat.cast_one, one_mul, outputCredit, UniformInt.lintegral_law]
    using sum_credit_le o n hn T 1 hOne F

/-- A finite horizon makes the cutoff mass smaller than any positive auxiliary credit. -/
theorem exists_horizon (n : ℕ) (hn : 0 < n) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T : ℕ, ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T ≤ ε := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ m =>
    by_cases hm : m = 0
    · subst m
      exact ⟨0, by simp⟩
    · have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm
      have hsmall : 0 < ε / (m : ℝ≥0∞) := ENNReal.div_pos hε.ne' (by finiteness)
      obtain ⟨T, hT⟩ := ENNReal.exists_pow_mul_ge_one hsmall (by norm_num : (1 : ℝ≥0) < 2)
      refine ⟨T, ?_⟩
      simp only [Nat.add_one_sub_one]
      apply (ENNReal.div_le_iff (by positivity) (by finiteness)).mpr
      calc
        (m : ℝ≥0∞) = 1 * m := by simp
        _ ≤ (ε / m * (2 : ℝ≥0∞) ^ T) * m := by
          simpa only [mul_comm, ENNReal.coe_two] using mul_le_mul_right hT m
        _ = ε * 2 ^ T := by
          rw [mul_right_comm, ENNReal.div_mul_cancel hm0 (by finiteness)]

end

end SampLib.BitRecycler
