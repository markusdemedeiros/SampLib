module

public import SampLib.Constants.Laws.EulerSondow

@[expose] public section

/-! # Tail bounds for the Euler constant series

Inverse-square differences bound the ordinary tail. Summing those bounds over the binary
lengths bounds the weighted tail that the sampler leaves unread.
-/

open Finset Filter

namespace SampLib.EulerSondow

noncomputable section

/-- The inverse-square discrete derivative controls the kernel's ordinary tail. -/
theorem delta_le_square_difference (n : ℕ) (hn : 1 ≤ n) :
    delta (n + 1) ≤ 1 / (16 * (n : ℝ) ^ 2) - 1 / (16 * ((n : ℝ) + 1) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by positivity
  unfold delta
  push_cast
  apply (le_sub_iff_add_le).mpr
  field_simp
  nlinarith [sq_nonneg (n : ℝ)]

/-- The unweighted tail is bounded by the initial inverse-square majorant. -/
theorem tail_le_square (m : ℕ) (hm : 1 ≤ m) : tail (m + 1) ≤ 1 / (16 * (m : ℝ) ^ 2) := by
  rw [← (tail_hasSum (m + 1) (by omega)).tsum_eq]
  apply Real.tsum_le_of_sum_range_le (fun n => delta_nonneg (n + (m + 1)))
  intro N
  have h : (∑ n ∈ range N, delta (n + (m + 1))) ≤
      1 / (16 * (m : ℝ) ^ 2) - 1 / (16 * ((N + m : ℕ) : ℝ) ^ 2) := by
    induction N with
    | zero => simp
    | succ N IH =>
      rw [sum_range_succ]
      have ht := delta_le_square_difference (N + m) (by omega)
      push_cast at IH ht ⊢
      convert (add_le_add IH ht) using 1; ring
  exact h.trans (sub_le_self _ (by positivity))

private theorem threshold_truncated_column (k N : ℕ) (hk : k.size ≤ N) :
    (∑ j ∈ range N, thresholdKernel j k) = (k.size : ℝ) * delta k := by
  rw [← threshold_column]
  symm
  apply tsum_eq_sum
  intro j hj
  have hjN : N ≤ j := by simpa only [mem_range, not_lt] using hj
  have hnot : ¬2 ^ j ≤ k := by
    intro h
    have hj' : j < k.size := Nat.lt_size.mpr h
    omega
  simp [thresholdKernel, hnot]

private theorem threshold_prefix (n j : ℕ) (hj : j < n.size) :
    (∑ k ∈ range (n + 1), thresholdKernel j k) = tail (2 ^ j) - tail (n + 1) := by
  have h := (threshold_summable j).sum_add_tsum_nat_add (n + 1)
  have hjn : 2 ^ j ≤ n := Nat.lt_size.mp hj
  have hshift : (fun k => thresholdKernel j (k + (n + 1))) =
      (fun k => delta (k + (n + 1))) := by
    funext k
    have hle : 2 ^ j ≤ k + (n + 1) := by omega
    simp [thresholdKernel, hle]
  rw [hshift, (tail_hasSum (n + 1) (by omega)).tsum_eq, threshold_row] at h
  linarith

/-- A finite weighted prefix is a dyadic prefix minus one shared ordinary tail. -/
theorem weighted_prefix (n : ℕ) :
    (∑ k ∈ range (n + 1), (k.size : ℝ) * delta k) =
      (∑ j ∈ range n.size, tail (2 ^ j)) - (n.size : ℝ) * tail (n + 1) := by
  calc
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range n.size, thresholdKernel j k := by
      apply sum_congr rfl
      intro k hk
      apply (threshold_truncated_column k n.size ?_).symm
      exact Nat.size_le.mpr ((Nat.le_of_lt_succ (mem_range.mp hk)).trans_lt (Nat.lt_size_self n))
    _ = ∑ j ∈ range n.size, ∑ k ∈ range (n + 1), thresholdKernel j k := sum_comm
    _ = ∑ j ∈ range n.size, (tail (2 ^ j) - tail (n + 1)) := by
      apply sum_congr rfl
      intro j hj
      exact threshold_prefix n j (mem_range.mp hj)
    _ = _ := by simp [sum_sub_distrib]

/-- Beyond `n`, existing binary digits pay the ordinary tail, and new digits pay dyadic tails. -/
theorem weighted_tail_eq (n : ℕ) :
    (∑' k, ((k + (n + 1)).size : ℝ) * delta (k + (n + 1))) =
      (n.size : ℝ) * tail (n + 1) + ∑' j, tail (2 ^ (j + n.size)) := by
  have hw := weighted_hasSum.summable.sum_add_tsum_nat_add (n + 1)
  have hd := dyadic_hasSum.summable.sum_add_tsum_nat_add n.size
  rw [weighted_prefix, weighted_hasSum.tsum_eq] at hw
  rw [dyadic_hasSum.tsum_eq] at hd
  linarith

private theorem dyadic_threshold (n j : ℕ) : n * 2 ^ j ≤ 2 ^ (j + n.size) - 1 := by
  have h := Nat.mul_le_mul_left (2 ^ j) (Nat.succ_le_of_lt (Nat.lt_size_self n))
  rw [Nat.mul_succ, ← pow_add, Nat.mul_comm (2 ^ j) n] at h
  have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  omega

private theorem dyadic_tail_point (n j : ℕ) (hn : 1 ≤ n) :
    tail (2 ^ (j + n.size)) ≤ (1 / (16 * (n : ℝ) ^ 2)) * (1 / 4 : ℝ) ^ j := by
  have hb := dyadic_threshold n j
  have hp : 0 < n * 2 ^ j := Nat.mul_pos (by omega) (by positivity)
  have hm : 1 ≤ 2 ^ (j + n.size) - 1 := by omega
  have he : 2 ^ (j + n.size) - 1 + 1 = 2 ^ (j + n.size) := by omega
  have ht := tail_le_square (2 ^ (j + n.size) - 1) hm
  rw [he] at ht
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (n : ℝ) * (2 : ℝ) ^ j ≤ ((2 ^ (j + n.size) - 1 : ℕ) : ℝ) := by
    exact_mod_cast hb
  have hpow : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    _ ≤ 1 / (16 * (((2 ^ (j + n.size) - 1 : ℕ) : ℝ)) ^ 2) := ht
    _ ≤ 1 / (16 * ((n : ℝ) * (2 : ℝ) ^ j) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    _ = _ := by
      rw [mul_pow, hpow, div_pow]
      norm_num
      field_simp

/-- New binary digits contribute a geometric sequence of inverse-square tails. -/
theorem dyadic_tail_le (n : ℕ) (hn : 1 ≤ n) :
    (∑' j, tail (2 ^ (j + n.size))) ≤ 1 / (12 * (n : ℝ) ^ 2) := by
  have hg : HasSum (fun j : ℕ => (1 / 4 : ℝ) ^ j) (4 / 3) := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1) using 1; norm_num
  apply Real.tsum_le_of_sum_range_le (fun j => tail_nonneg _ (by positivity))
  intro N
  calc
    _ ≤ (1 / (16 * (n : ℝ) ^ 2)) * ∑ j ∈ range N, (1 / 4 : ℝ) ^ j := by
      rw [mul_sum]
      exact sum_le_sum fun j _ => dyadic_tail_point n j hn
    _ ≤ (1 / (16 * (n : ℝ) ^ 2)) * (4 / 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [hg.tsum_eq] using hg.summable.sum_le_tsum (range N) (fun j _ => by positivity)
    _ = _ := by ring

/-- The source's stated rational remainder bounds the complete positive-series tail. -/
theorem weighted_tail_le (n : ℕ) (hn : 1 ≤ n) :
    (∑' k, ((k + (n + 1)).size : ℝ) * delta (k + (n + 1))) ≤
      (((2 + n.size) * n + 1 : ℕ) : ℝ) / (16 * (n : ℝ) ^ 3) := by
  rw [weighted_tail_eq]
  have ht := tail_le_square n hn
  have hd := dyadic_tail_le n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (n.size : ℝ) * (1 / (16 * (n : ℝ) ^ 2)) + 1 / (12 * (n : ℝ) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left ht (by positivity)) hd
    _ ≤ _ := by
      push_cast
      field_simp
      nlinarith

end

end SampLib.EulerSondow
