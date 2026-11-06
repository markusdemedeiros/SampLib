import SampLib.Weighted.Laws.EntropyPoolStopped

/-! # Output masses of an entropy pool

The stopped functional is a finite matrix of point masses. Its unresolved tail
vanishes, so the masses of a bounded-width pool sum to one, and averaging the ranks
of a uniform pool gives each output the same mass.
-/

open Finset MeasureTheory Filter
open scoped ENNReal Topology

namespace SampLib.EntropyPool

noncomputable section

private def point (r x : ℕ) : ℝ≥0∞ := if x = r then 1 else 0

/-- The finite stopped functional is its matrix of accepted point masses. -/
theorem stopped_finite (n T width value : ℕ) (F : ℕ → ℝ≥0∞) :
    stopped n T width value F =
      ∑ r ∈ range n, stopped n T width value (point r) * F r := by
  have hF : ∀ x, x < n → F x = ∑ r ∈ range n, point r x * F r := by
    intro x hx
    simp [point, hx]
  rw [stopped_congr n T width value F _ hF, stopped_sum]
  apply sum_congr rfl
  intro r _
  exact stopped_mul n T width value (point r) (F r)

/-- Total mass of all finite accepting leaves with the indicated output. -/
def mass (n width value r : ℕ) : ℝ≥0∞ := ⨆ T, stopped n T width value (point r)

theorem mass_le_one (n width value r : ℕ) : mass n width value r ≤ 1 := by
  apply iSup_le
  intro T
  exact (stopped_mono n T width value (point r) (fun _ => 1)
    (fun x => by by_cases hx : x = r <;> simp [point, hx])).trans (stopped_one_le n T width value)

theorem stopped_le_mass (n T width value r : ℕ) :
    stopped n T width value (point r) ≤ mass n width value r :=
  le_iSup (fun U => stopped n U width value (point r)) T

/-- A finite-horizon program needs no more than the eventual output expectation plus cutoff mass. -/
theorem horizon_bound (n T width value : ℕ) (F : ℕ → ℝ≥0∞) :
    BitRecycler.credit .lower n F T width value ≤
      (∑ r ∈ range n, mass n width value r * F r) +
        BitRecycler.credit .lower n (fun _ => 0) T width value := by
  rw [credit_eq_stopped_add_tail, stopped_finite]
  exact add_le_add (sum_le_sum fun r _ =>
    mul_le_mul' (stopped_le_mass n T width value r) le_rfl) le_rfl

private theorem tail_one_le (n T width value : ℕ) :
    BitRecycler.credit .lower n (fun _ => 0) T width value ≤ 1 := by
  calc
    _ ≤ stopped n T width value (fun _ => 1) +
        BitRecycler.credit .lower n (fun _ => 0) T width value := le_add_left le_rfl
    _ = 1 := stopped_one_add_tail n T width value

private theorem tail_antitone (n width value : ℕ) :
    Antitone (fun T => BitRecycler.credit .lower n (fun _ => 0) T width value) := by
  apply antitone_nat_of_succ_le
  intro T
  induction T generalizing width value with
  | zero => simpa only [BitRecycler.credit_zero] using tail_one_le n 1 width value
  | succ T IH =>
    unfold BitRecycler.credit
    apply ENNReal.div_le_div_right _ 2
    exact sum_le_sum fun b _ => kernel_mono _ _ _ _ _ _ _ (fun _ => le_rfl) IH

/-- No single fixed rank receives more cutoff credit than the full retained interval. -/
theorem tail_le (n T width value : ℕ) (hn : 0 < n) (hw : width < n) (hv : value < width) :
    BitRecycler.credit .lower n (fun _ => 0) T width value ≤
      ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  calc
    _ ≤ ∑ v ∈ range width, BitRecycler.credit .lower n (fun _ => 0) T width v :=
      single_le_sum (fun _ _ => bot_le) (mem_range.mpr hv)
    _ ≤ _ := by
      simpa [BitRecycler.outputCredit] using BitRecycler.sum_credit_le .lower n hn T width hw
        (fun _ => 0)

/-- Each fixed valid rank has exponentially vanishing unabsorbed mass. -/
theorem tail_tendsto (n width value : ℕ) (hn : 0 < n) (hw : width < n) (hv : value < width) :
    Tendsto (fun T => BitRecycler.credit .lower n (fun _ => 0) T width value)
      atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨T, hT⟩ := BitRecycler.exists_horizon n hn ε hε
  filter_upwards [eventually_ge_atTop T] with N hTN
  exact ((tail_antitone n width value hTN).trans (tail_le n T width value hn hw hv)).trans hT

/-- Summing all finite accepting leaves gives a normalized fixed-state law. -/
theorem sum_mass (n width value : ℕ) (hn : 0 < n) (hw : width < n) (hv : value < width) :
    ∑ r ∈ range n, mass n width value r = 1 := by
  have hm : Tendsto (fun T => ∑ r ∈ range n, stopped n T width value (point r)) atTop
      (nhds (∑ r ∈ range n, mass n width value r)) := by
    apply tendsto_finsetSum
    intro r _
    exact tendsto_atTop_iSup (stopped_mono_time n width value (point r))
  have hp : Tendsto (fun T => stopped n T width value (fun _ => 1)) atTop
      (nhds (∑ r ∈ range n, mass n width value r)) := by
    have heq : (fun T => stopped n T width value (fun _ => 1)) =
        fun T => ∑ r ∈ range n, stopped n T width value (point r) := by
      funext T
      simpa only [mul_one] using stopped_finite n T width value (fun _ => 1)
    rw [heq]
    exact hm
  have hlim := hp.add (tail_tendsto n width value hn hw hv)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop
      (nhds (∑ r ∈ range n, mass n width value r)) := by
    simpa only [stopped_one_add_tail, add_zero] using hlim
  exact tendsto_nhds_unique hconst tendsto_const_nhds

private theorem sum_bits (F : ℕ → ℝ≥0∞) (width : ℕ) :
    (∑ v ∈ range width, ∑ b ∈ range 2, F (v * 2 + b)) = ∑ x ∈ range (width * 2), F x := by
  simpa only [Nat.mul_comm] using (WordIntervals.sum_blocks 2 width F).symm

private theorem sum_stopped_succ (n T width : ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ v ∈ range width, stopped n (T + 1) width v F) =
      (∑ x ∈ range (width * 2), BitRecycler.kernel .lower n F
        (fun w v => stopped n T w v F) (width * 2) x) / 2 := by
  simp only [stopped, ENNReal.div_eq_inv_mul, mul_sum]
  rw [← sum_bits]

/-- Uniform ranks expose every accepted output equally, at each finite horizon. -/
private theorem bulk_point (n T width r s : ℕ) (hw : width < n) (hr : r < n) (hs : s < n) :
    (∑ v ∈ range width, stopped n T width v (point r)) =
      ∑ v ∈ range width, stopped n T width v (point s) := by
  induction T generalizing width with
  | zero => simp [stopped]
  | succ T IH =>
    rw [sum_stopped_succ, sum_stopped_succ]
    by_cases hwide : n ≤ width * 2
    · rw [BitRecycler.kernel_sum .lower n (width * 2) hwide,
        BitRecycler.kernel_sum .lower n (width * 2) hwide]
      have htail : width * 2 - n < n := by omega
      rw [IH _ htail]
      simp [point, hr, hs]
    · simp only [BitRecycler.kernel, ite_eq_right hwide]
      rw [IH _ (by omega)]

/-- The point-mass matrix has equal column sums under a uniform initial rank. -/
theorem bulk_mass (n width r s : ℕ) (hw : width < n) (hr : r < n) (hs : s < n) :
    (∑ v ∈ range width, mass n width v r) = ∑ v ∈ range width, mass n width v s := by
  have hR : Tendsto (fun T => ∑ v ∈ range width, stopped n T width v (point r)) atTop
      (nhds (∑ v ∈ range width, mass n width v r)) := by
    apply tendsto_finsetSum
    intro v _
    exact tendsto_atTop_iSup (stopped_mono_time n width v (point r))
  have hS : Tendsto (fun T => ∑ v ∈ range width, stopped n T width v (point s)) atTop
      (nhds (∑ v ∈ range width, mass n width v s)) := by
    apply tendsto_finsetSum
    intro v _
    exact tendsto_atTop_iSup (stopped_mono_time n width v (point s))
  have heq : (fun T => ∑ v ∈ range width, stopped n T width v (point r)) =
      fun T => ∑ v ∈ range width, stopped n T width v (point s) := by
    funext T
    exact bulk_point n T width r s hw hr hs
  rw [heq] at hR
  exact tendsto_nhds_unique hR hS

/-- Averaging all valid ranks gives a uniform output; individual ranks retain their actual bias. -/
theorem uniform_mass (n width r : ℕ) (hn : 0 < n) (hw : width < n) (hr : r < n) :
    (∑ v ∈ range width, mass n width v r) = (width : ℝ≥0∞) / n := by
  have htotal : (∑ s ∈ range n, ∑ v ∈ range width, mass n width v s) = width := by
    rw [sum_comm]
    calc
      _ = ∑ v ∈ range width, (1 : ℝ≥0∞) := sum_congr rfl fun v hv =>
        sum_mass n width v hn hw (mem_range.mp hv)
      _ = _ := by simp
  apply (ENNReal.eq_div_iff (by exact_mod_cast hn.ne') (by finiteness)).mpr
  calc
    _ = ∑ s ∈ range n, ∑ v ∈ range width, mass n width v r := by simp
    _ = ∑ s ∈ range n, ∑ v ∈ range width, mass n width v s :=
      sum_congr rfl fun s hs => bulk_mass n width r s hw hr (mem_range.mp hs)
    _ = width := htotal

end

end SampLib.EntropyPool
