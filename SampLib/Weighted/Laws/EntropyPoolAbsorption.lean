import SampLib.Weighted.Laws.EntropyPool
import SampLib.Common.Laws.BitRecycler

/-! # Finite-leaf laws for an exact entropy pool

Once a pool needs a fresh bit, its width is below the requested bound. Every
subsequent acceptance therefore has quotient one and resets the pool to `(0,1)`.
The finite stopped laws retain each fixed rank's actual bias; only averaging all
ranks of a uniform pool gives a uniform output.
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

private theorem kernel_mono (n width value : ℕ) (F G : ℕ → ℝ≥0∞)
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

/-- The finite-leaf output measure from one fixed bounded-width rank. -/
def boundedKernel (n width value : ℕ) : Measure ℕ :=
  ∑ r ∈ range n, (mass n width value r • Measure.dirac r)

/-- Valid bounded-width states absorb almost surely; the rank need not be uniform. -/
def boundedLaw (n width value : ℕ) (_hn : 0 < n) (_hw : width < n)
    (_hv : value < width) : Measure ℕ := boundedKernel n width value

instance (n width value : ℕ) (hn : 0 < n) (hw : width < n) (hv : value < width) :
    IsProbabilityMeasure (boundedLaw n width value hn hw hv) where
  measure_univ := by simpa [boundedLaw, boundedKernel] using sum_mass n width value hn hw hv

/-- The fixed-rank law accepts arbitrary, possibly infinite continuation credits. -/
theorem lintegral_boundedKernel (n width value : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ r, F r ∂boundedKernel n width value) =
      ∑ r ∈ range n, mass n width value r * F r := by
  simp [boundedKernel, lintegral_finsetSum_measure]

theorem boundedKernel_singleton (n width value r : ℕ) :
    boundedKernel n width value {r} = if r < n then mass n width value r else 0 := by
  simp [boundedKernel, Pi.single_apply, eq_comm]

/-- Averaging the fixed-state kernels exposes the uniform law, with no restriction on credits. -/
theorem ensemble_expectation (n width : ℕ) (hn : 0 < n) (hw : width < n)
    (F : ℕ → ℝ≥0∞) :
    (∑ v ∈ range width, ∫⁻ r, F r ∂boundedKernel n width v) =
      ((width : ℝ≥0∞) / n) * ∑ r ∈ range n, F r := by
  simp_rw [lintegral_boundedKernel]
  rw [sum_comm]
  calc
    _ = ∑ r ∈ range n, ((width : ℝ≥0∞) / n) * F r := by
      apply sum_congr rfl
      intro r hr
      rw [← sum_mul, uniform_mass n width r hn hw (mem_range.mp hr)]
    _ = _ := (mul_sum _ _ _).symm

/-- The actual initial pool has a uniform output law and no retained quotient. -/
theorem reset_expectation (n : ℕ) (hn : 0 < n) (hlarge : 1 < n) (F : ℕ → ℝ≥0∞) :
    (∫⁻ r, F r ∂boundedLaw n 1 0 hn hlarge (by decide)) =
      ∫⁻ r, F r ∂UniformInt.law n := by
  change (∫⁻ r, F r ∂boundedKernel n 1 0) = _
  rw [UniformInt.lintegral_law]
  simpa only [sum_range_one, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
    ensemble_expectation n 1 hn hlarge F

/-- Expected eventual credit and the explicit geometric tail fund a finite source execution. -/
theorem horizon_lintegral_bound (n T width value : ℕ) (F : ℕ → ℝ≥0∞)
    (hn : 0 < n) (hw : width < n) (hv : value < width) :
    BitRecycler.credit .lower n F T width value ≤
      (∫⁻ r, F r ∂boundedLaw n width value hn hw hv) +
        ((n - 1 : ℕ) : ℝ≥0∞) / 2 ^ T := by
  change _ ≤ (∫⁻ r, F r ∂boundedKernel n width value) + _
  rw [lintegral_boundedKernel]
  exact (horizon_bound n T width value F).trans
    (add_le_add le_rfl (tail_le n T width value hn hw hv))

end

end SampLib.EntropyPool
