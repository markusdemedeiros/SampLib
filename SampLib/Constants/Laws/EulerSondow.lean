module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Data.Nat.Size
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic

@[expose] public section

/-! # The positive binary-length series for Euler's constant

The kernel is a difference of harmonic tails. Summing those tails at powers of
two telescopes along the ordinary harmonic definition of Euler's constant.
-/

open Finset Filter

namespace SampLib.EulerSondow

noncomputable section

/-- The positive rational kernel in the source's Sondow series. -/
def delta (n : ℕ) : ℝ := 1 / (2 * n * (2 * n + 1) * (2 * n + 2))

/-- The harmonic expression for the tail beginning at a positive integer. -/
def tail (n : ℕ) : ℝ :=
  (harmonic (2 * n - 1) : ℝ) - (harmonic (n - 1) : ℝ) - Real.log 2 - 1 / (4 * n)

theorem delta_nonneg (n : ℕ) : 0 ≤ delta n := by unfold delta; positivity

private theorem harmonic_step (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) = (harmonic (n - 1) : ℝ) + 1 / (n : ℝ) := by
  have he : n - 1 + 1 = n := by omega
  have h := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ (n - 1))
  simpa only [he, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, one_div] using h

/-- Partial fractions make the telescoping harmonic argument explicit. -/
theorem delta_partial_fraction (n : ℕ) (hn : 0 < n) :
    delta n = 1 / (4 * (n : ℝ)) - 1 / (2 * n + 1) + 1 / (4 * (n + 1)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold delta
  field_simp
  ring

/-- The kernel is the discrete derivative of the harmonic tail. -/
theorem delta_eq_difference (n : ℕ) (hn : 0 < n) : delta n = tail n - tail (n + 1) := by
  have h₁ := harmonic_step n hn
  have h₂ := harmonic_step (2 * n) (by omega)
  have h₃ := harmonic_step (2 * n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h₃
  have he : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  simp only [tail, Nat.add_sub_cancel, he]
  rw [h₃, h₂, h₁]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold delta
  push_cast
  field_simp
  ring

private theorem tail_eq_sequences (n : ℕ) (hn : 0 < n) :
    tail n = Real.eulerMascheroniSeq (2 * n - 1) -
      Real.eulerMascheroniSeq (n - 1) - 1 / (4 * (n : ℝ)) := by
  have he₁ : 2 * n - 1 + 1 = 2 * n := by omega
  have he₂ : n - 1 + 1 = n := by omega
  have hr₁ : ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) := by exact_mod_cast he₁
  have hr₂ : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast he₂
  simp only [tail, Real.eulerMascheroniSeq, hr₁, hr₂]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num) hn']
  ring

/-- Both harmonic sequences tend to Euler's constant, leaving no residual tail. -/
theorem tail_tendsto : Tendsto tail atTop (nhds 0) := by
  have h₂ : Tendsto (fun n : ℕ => 2 * n - 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n - 1) tendsto_id
  have h₁ := tendsto_sub_atTop_nat 1
  have hi : Tendsto (fun n : ℕ => 1 / (4 * (n : ℝ))) atTop (nhds 0) := by
    have h : Tendsto (fun n : ℕ => (4 : ℝ)⁻¹ * (n : ℝ)⁻¹) atTop (nhds ((4 : ℝ)⁻¹ * 0)) :=
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_zero, zero_mul, mul_comm] using h
  have h := ((Real.tendsto_eulerMascheroniSeq.comp h₂).sub
    (Real.tendsto_eulerMascheroniSeq.comp h₁)).sub hi
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (tail_eq_sequences n (by omega)).symm

/-- Finite consecutive kernels telescope exactly, before taking any limit. -/
theorem partial_sum (m N : ℕ) (hm : 0 < m) :
    (∑ n ∈ range N, delta (n + m)) = tail m - tail (N + m) := by
  induction N with
  | zero => simp
  | succ N IH =>
    rw [sum_range_succ, IH, delta_eq_difference (N + m) (by omega)]
    rw [show N + 1 + m = N + m + 1 by omega]
    ring

/-- The harmonic tail is the ordinary sum of the positive rational kernel. -/
theorem tail_hasSum (m : ℕ) (hm : 0 < m) : HasSum (fun n => delta (n + m)) (tail m) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => delta_nonneg (n + m)) _).2
  have h : Tendsto (fun N => tail m - tail (N + m)) atTop (nhds (tail m - 0)) :=
    tendsto_const_nhds.sub (tail_tendsto.comp (tendsto_add_atTop_nat m))
  simp_rw [partial_sum m _ hm]
  simpa only [sub_zero] using h

theorem delta_summable : Summable delta :=
  (summable_nat_add_iff 1).mp (tail_hasSum 1 (by norm_num)).summable

theorem tail_nonneg (m : ℕ) (hm : 0 < m) : 0 ≤ tail m := by
  rw [← (tail_hasSum m hm).tsum_eq]
  exact tsum_nonneg fun n => delta_nonneg (n + m)

private theorem dyadic_tail (k : ℕ) :
    tail (2 ^ k) = Real.eulerMascheroniSeq (2 ^ (k + 1) - 1) -
      Real.eulerMascheroniSeq (2 ^ k - 1) - (1 / 4 : ℝ) * (1 / 2) ^ k := by
  rw [tail_eq_sequences (2 ^ k) (by positivity), pow_succ']
  congr 1
  push_cast
  rw [div_pow]
  norm_num
  field_simp

/-- Summing the harmonic tails at powers of two removes every interior endpoint. -/
theorem dyadic_partial_sum (N : ℕ) :
    (∑ k ∈ range N, tail (2 ^ k)) = Real.eulerMascheroniSeq (2 ^ N - 1) -
      (1 / 4 : ℝ) * ∑ k ∈ range N, (1 / 2 : ℝ) ^ k := by
  induction N with
  | zero => simp [Real.eulerMascheroniSeq_zero]
  | succ N IH =>
    rw [sum_range_succ, IH, dyadic_tail, sum_range_succ]
    ring

/-- The dyadic harmonic differences sum to `γ-1/2`. -/
theorem dyadic_hasSum : HasSum (fun k => tail (2 ^ k)) (Real.eulerMascheroniConstant - 1 / 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => tail_nonneg (2 ^ k) (by positivity)) _).2
  simp_rw [dyadic_partial_sum]
  have hp := (tendsto_sub_atTop_nat 1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  have hh := Real.tendsto_eulerMascheroniSeq.comp hp
  have hg : Tendsto (fun N => ∑ k ∈ range N, (1 / 2 : ℝ) ^ k) atTop (nhds 2) := by
    convert (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).tendsto_sum_nat using 1; norm_num
  have hs : Tendsto (fun N => (1 / 4 : ℝ) * ∑ k ∈ range N, (1 / 2 : ℝ) ^ k)
      atTop (nhds ((1 / 4 : ℝ) * 2)) := tendsto_const_nhds.mul hg
  convert hh.sub hs using 1 <;> norm_num

/-- The kernel restricted to indices at least `2 ^ k`. -/
def thresholdKernel (k n : ℕ) : ℝ := if 2 ^ k ≤ n then delta n else 0

private theorem threshold_nonneg (k n : ℕ) : 0 ≤ thresholdKernel k n := by
  unfold thresholdKernel
  split_ifs <;> first | exact delta_nonneg n | exact le_rfl

theorem threshold_summable (k : ℕ) : Summable (thresholdKernel k) := by
  apply delta_summable.of_nonneg_of_le (threshold_nonneg k)
  intro n
  unfold thresholdKernel
  split_ifs <;> first | exact le_rfl | exact delta_nonneg n

/-- Each row of the threshold kernel sums to a dyadic tail. -/
theorem threshold_row (k : ℕ) : ∑' n, thresholdKernel k n = tail (2 ^ k) := by
  have h := (threshold_summable k).sum_add_tsum_nat_add (2 ^ k)
  have hzero : (∑ n ∈ range (2 ^ k), thresholdKernel k n) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp [thresholdKernel, not_le.mpr (mem_range.mp hn)]
  have hshift : (fun n => thresholdKernel k (n + 2 ^ k)) = (fun n => delta (n + 2 ^ k)) := by
    funext n
    simp [thresholdKernel]
  rw [hzero, zero_add, hshift, (tail_hasSum (2 ^ k) (by positivity)).tsum_eq] at h
  exact h.symm

/-- Each column of the threshold kernel counts the binary length. -/
theorem threshold_column (n : ℕ) :
    (∑' k, thresholdKernel k n) = (n.size : ℝ) * delta n := by
  calc
    _ = ∑ k ∈ range n.size, thresholdKernel k n := by
      apply tsum_eq_sum
      intro k hk
      have hkn : n.size ≤ k := by simpa only [mem_range, not_lt] using hk
      have hnot : ¬2 ^ k ≤ n := by
        intro h
        have hk' : k < n.size := Nat.lt_size.mpr h
        omega
      simp [thresholdKernel, hnot]
    _ = (n.size : ℝ) * delta n := by
      have h : ∀ k ∈ range n.size, thresholdKernel k n = delta n := by
        intro k hk
        simp [thresholdKernel, Nat.lt_size.mp (mem_range.mp hk)]
      rw [sum_congr rfl h]
      simp

/-- Binary length counts the dyadic thresholds below `n`; Tonelli sums their harmonic tails. -/
theorem weighted_hasSum : HasSum (fun n => (n.size : ℝ) * delta n)
    (Real.eulerMascheroniConstant - 1 / 2) := by
  have hp : Summable (fun z : ℕ × ℕ => thresholdKernel z.1 z.2) :=
    (summable_prod_of_nonneg (fun z => threshold_nonneg z.1 z.2)).mpr
      ⟨threshold_summable, by simpa only [threshold_row] using dyadic_hasSum.summable⟩
  have hw : Summable (fun n => (n.size : ℝ) * delta n) := by
    simpa only [Prod.fst_swap, Prod.snd_swap, threshold_column] using hp.prod_symm.prod
  have he : (∑' n, (n.size : ℝ) * delta n) = Real.eulerMascheroniConstant - 1 / 2 := by
    calc
      _ = ∑' n, ∑' k, thresholdKernel k n := by simp only [threshold_column]
      _ = ∑' k, ∑' n, thresholdKernel k n :=
        Summable.tsum_comm (f := thresholdKernel) hp
      _ = ∑' k, tail (2 ^ k) := by simp only [threshold_row]
      _ = _ := dyadic_hasSum.tsum_eq
  rw [← he]
  exact hw.hasSum

/-- The source's initial half plus the positive binary-length terms. -/
def term (n : ℕ) : ℝ := if n = 0 then 1 / 2 else (n.size : ℝ) * delta n

/-- The sampler's positive rational series is exactly Euler's constant. -/
theorem hasSum_term : HasSum term Real.eulerMascheroniConstant := by
  have hzero : HasSum (fun n : ℕ => if n = 0 then (1 / 2 : ℝ) else 0) (1 / 2) :=
    hasSum_ite_eq 0 (1 / 2)
  have h := hzero.add weighted_hasSum
  convert h using 1
  · funext n
    by_cases hn : n = 0 <;> simp [term, hn]
  · ring

end

end SampLib.EulerSondow
