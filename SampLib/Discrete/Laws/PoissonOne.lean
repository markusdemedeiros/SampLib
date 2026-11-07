import SampLib.Common.Laws.PoissonTree
import SampLib.Uniform.Laws.RndInt

/-! # Unit-rate Poisson rank kernel

One uniform rank moves the subset tree up, down, or to absorption. The gap to the
boundary is a potential that pays for the termination credit of each live child.
-/

open scoped ENNReal

namespace SampLib.PoissonOne

noncomputable section

open PoissonTree
open MeasureTheory Finset

def rankKernel (a b : ℕ) (T U D : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if j < b then T else if j = a then U else D

private theorem rank_mean (a b : ℕ) (hb : b ≤ a) (T U D : ℝ≥0∞) :
    (∫⁻ j, rankKernel a b T U D j ∂RndInt.law a) =
      ((b : ℝ≥0∞) * T + U + (a - b : ℕ) * D) / (a + 1) := by
  have hprefix : (∑ j ∈ range a, rankKernel a b T U D j) =
      (b : ℝ≥0∞) * T + (a - b : ℕ) * D := by
    have hreduce : (∑ j ∈ range a, rankKernel a b T U D j) =
        ∑ j ∈ range a, if j < b then T else D := by
      apply sum_congr rfl
      intro j hj
      simp [rankKernel, Nat.ne_of_lt (mem_range.mp hj)]
    rw [hreduce]
    conv_lhs => rw [← Nat.add_sub_of_le hb, sum_range_add]
    have hfirst : (∑ j ∈ range b, if j < b then T else D) = b * T := by
      calc
        _ = ∑ j ∈ range b, T := sum_congr rfl fun j hj => ite_eq_left (mem_range.mp hj)
        _ = _ := by simp [nsmul_eq_mul]
    rw [hfirst]
    simp [Nat.not_lt.mpr (Nat.le_add_right b _), nsmul_eq_mul]
  rw [RndInt.expectation, sum_range_succ, hprefix]
  simp only [rankKernel, Nat.not_lt.mpr hb, ite_false, ite_true,
    Nat.cast_add, Nat.cast_one]
  congr 1
  ring

def budget (s : State) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  credit s F + ε * (s.size - s.boundary : ℕ)

def rankCredit (s : State) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  rankKernel s.size s.boundary (F s.count)
    (budget s.up F ε + 2 * ε) (budget s.down F ε + 2 * ε)

/-- A live child receives its potential budget and twice the common termination
credit. Their expected total is at most the current potential budget. -/
theorem expectation (s : State) (hb : s.boundary ≤ s.size)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (ha : ε = 0 ∨ 2 ≤ s.size) :
    (∫⁻ j, rankCredit s F ε j ∂RndInt.law s.size) ≤ budget s F ε + ε := by
  have hdu : s.up.size - s.up.boundary = s.size - s.boundary + 1 := by
    dsimp only [State.up]
    omega
  have hdd : s.down.size - s.down.boundary = 0 := by simp [State.down]
  have hexact : (∫⁻ j, rankCredit s F ε j ∂RndInt.law s.size) =
      credit s F + ε * ((3 : ℝ≥0∞) * (s.size - s.boundary + 1 : ℕ) / (s.size + 1)) := by
    rw [rankCredit, rank_mean s.size s.boundary hb]
    rw [credit_recurrence s F]
    simp only [budget, hdu, hdd, Nat.cast_zero, mul_zero, add_zero,
      ENNReal.div_eq_inv_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hexact]
  rcases ha with rfl | ha
  · simp [budget]
  · have hcoef : (3 : ℝ≥0∞) * (s.size - s.boundary + 1 : ℕ) / (s.size + 1) ≤
        (s.size - s.boundary + 1 : ℕ) := by
      apply (ENNReal.div_le_iff (by positivity) (by finiteness)).mpr
      have hthree : (3 : ℝ≥0∞) ≤ s.size + 1 := by
        exact_mod_cast (show 3 ≤ s.size + 1 by omega)
      simpa only [mul_comm] using
        mul_le_mul_left hthree (((s.size - s.boundary + 1 : ℕ) : ℝ≥0∞))
    calc
      _ ≤ credit s F + ε * (s.size - s.boundary + 1 : ℕ) :=
        add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul_left hcoef ε)
      _ = _ := by simp only [budget, Nat.cast_add, Nat.cast_one]; ring

theorem termination_credit (δ : ℝ≥0∞) (hδ : 0 < δ) (d : ℕ) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ δ = ε * d + ε := by
  refine ⟨δ / (d + 1), ENNReal.div_pos hδ.ne' (by finiteness), ?_⟩
  have h : δ / (d + 1) * (d + 1) = δ :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one] at h
  exact h.symm

theorem rank_support (a : ℕ) : ∀ᵐ j ∂RndInt.law a, j ≤ a := by
  simp only [RndInt.law, UniformInt.law, Measure.uniformOfFinset,
    ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure _ ((range (a + 1)).card : ℝ≥0∞)⁻¹
  simpa using Nat.le_of_lt_succ (mem_range.mp hj)

end

end SampLib.PoissonOne
