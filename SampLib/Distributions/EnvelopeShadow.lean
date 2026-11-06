module

public import SampLib.Distributions.EnvelopeRescaling
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! # Shadow histories for reverse-time envelope rescaling

Conditioned on the current head count, the past is generated backwards by the
reverse binomial kernels. Thresholds are updated on every history, independently
of the cached uniform. Their conditional means remain the Bernstein bounds.
-/

open Finset

namespace SampLib.EnvelopeFactory

noncomputable section

/-- The finite reverse kernels and their consistent coefficient envelopes. -/
structure Scheme where
  degree : ℕ → ℕ
  initial_degree : degree 0 = 0
  grows : ∀ t, degree t < degree (t + 1)
  lower : (t : ℕ) → Fin (degree t + 1) → ℝ
  upper : (t : ℕ) → Fin (degree t + 1) → ℝ
  bounds : ∀ t k, 0 ≤ lower t k ∧ lower t k ≤ upper t k ∧ upper t k ≤ 1
  lower_initial : ∀ k, lower 0 k = 0
  upper_initial : ∀ k, upper 0 k = 1
  reverse : (t : ℕ) → Fin (degree (t + 1) + 1) → Fin (degree t + 1) → ℝ
  reverse_nonneg : ∀ t k j, 0 ≤ reverse t k j
  reverse_sum : ∀ t k, ∑ j, reverse t k j = 1
  lower_consistent : ∀ t k, mean (reverse t k) (lower t) ≤ lower (t + 1) k
  upper_consistent : ∀ t k, upper (t + 1) k ≤ mean (reverse t k) (upper t)

namespace Scheme

variable (s : Scheme)

def lowerBar (t : ℕ) (k : Fin (s.degree (t + 1) + 1)) : ℝ :=
  mean (s.reverse t k) (s.lower t)

def upperBar (t : ℕ) (k : Fin (s.degree (t + 1) + 1)) : ℝ :=
  mean (s.reverse t k) (s.upper t)

/-- A past records every earlier head count, ending immediately before the current row. -/
@[reducible] def Past (s : Scheme) : ℕ → Type
  | 0 => Unit
  | t + 1 => Past s t × Fin (s.degree t + 1)

@[reducible] instance pastFintype (t : ℕ) : Fintype (s.Past t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ t IH =>
    letI := IH
    exact inferInstanceAs (Fintype (s.Past t × Fin (s.degree t + 1)))

/-- Conditional history weights contain no division by the unknown input probability. -/
def weight (s : Scheme) : (t : ℕ) → Fin (s.degree t + 1) → s.Past t → ℝ
  | 0, _, _ => 1
  | t + 1, k, (h, j) => s.reverse t k j * weight s t j h

theorem weight_nonneg (t : ℕ) (k : Fin (s.degree t + 1)) (h : s.Past t) :
    0 ≤ s.weight t k h := by
  induction t with
  | zero => exact zero_le_one
  | succ t IH =>
    rcases h with ⟨h, j⟩
    exact mul_nonneg (s.reverse_nonneg t k j) (IH j h)

/-- Reverse conditioning averages over the previous row, then over its earlier past. -/
theorem mean_previous (t : ℕ) (k : Fin (s.degree (t + 1) + 1))
    (f : Fin (s.degree t + 1) → s.Past t → ℝ) :
    mean (s.weight (t + 1) k) (fun z => f z.2 z.1) =
      mean (s.reverse t k) (fun j => mean (s.weight t j) (f j)) := by
  simp only [mean, Past, weight, Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  ring

theorem weight_sum (t : ℕ) (k : Fin (s.degree t + 1)) : ∑ h, s.weight t k h = 1 := by
  induction t with
  | zero => simp [weight, Past]
  | succ t IH =>
    have h := s.mean_previous t k (fun _ _ => 1)
    simpa only [mean, mul_one, IH, s.reverse_sum] using h

/-- The source's thresholds, with total real division extending collapsed shadow histories. -/
def thresholds (s : Scheme) : (t : ℕ) → Fin (s.degree t + 1) → s.Past t → ℝ × ℝ
  | 0, _, _ => (0, 1)
  | t + 1, k, (h, j) =>
      let previous := thresholds s t j h
      (lowerUpdate previous.1 previous.2 (s.lowerBar t k) (s.upperBar t k) (s.lower (t + 1) k),
       upperUpdate previous.1 previous.2 (s.lowerBar t k) (s.upperBar t k) (s.upper (t + 1) k))

theorem thresholds_bounds (t : ℕ) (k : Fin (s.degree t + 1)) (h : s.Past t) :
    0 ≤ (s.thresholds t k h).1 ∧
      (s.thresholds t k h).1 ≤ (s.thresholds t k h).2 ∧
      (s.thresholds t k h).2 ≤ 1 := by
  induction t with
  | zero => exact ⟨le_rfl, zero_le_one, le_rfl⟩
  | succ t IH =>
    rcases h with ⟨h, j⟩
    obtain ⟨hL, hLU, hU⟩ := IH j h
    obtain ⟨hLL, hnext, hUU⟩ := updates_nested _ _ _ _ _ _ hLU
      (s.lower_consistent t k) (s.bounds (t + 1) k).2.1 (s.upper_consistent t k)
    exact ⟨hL.trans hLL, hnext, hUU.trans hU⟩

/-- Every extension shrinks the very same uniform interval. -/
theorem thresholds_nested (t : ℕ) (k : Fin (s.degree (t + 1) + 1))
    (h : s.Past t) (j : Fin (s.degree t + 1)) :
    (s.thresholds t j h).1 ≤ (s.thresholds (t + 1) k (h, j)).1 ∧
      (s.thresholds (t + 1) k (h, j)).1 ≤ (s.thresholds (t + 1) k (h, j)).2 ∧
      (s.thresholds (t + 1) k (h, j)).2 ≤ (s.thresholds t j h).2 :=
  updates_nested _ _ _ _ _ _ (s.thresholds_bounds t j h).2.1
    (s.lower_consistent t k) (s.bounds (t + 1) k).2.1 (s.upper_consistent t k)

/-- Conditional shadow means are exactly the current coefficients, not a pointwise target. -/
theorem thresholds_mean (t : ℕ) (k : Fin (s.degree t + 1)) :
    mean (s.weight t k) (fun h => (s.thresholds t k h).1) = s.lower t k ∧
      mean (s.weight t k) (fun h => (s.thresholds t k h).2) = s.upper t k := by
  induction t with
  | zero =>
    simp [mean, thresholds, weight, Past, s.lower_initial, s.upper_initial]
  | succ t IH =>
    have hL : mean (s.weight (t + 1) k)
        (fun z => (s.thresholds t z.2 z.1).1) = s.lowerBar t k := by
      rw [s.mean_previous t k (fun j h => (s.thresholds t j h).1)]
      simp only [fun j => (IH j).1]
      rfl
    have hU : mean (s.weight (t + 1) k)
        (fun z => (s.thresholds t z.2 z.1).2) = s.upperBar t k := by
      rw [s.mean_previous t k (fun j h => (s.thresholds t j h).2)]
      simp only [fun j => (IH j).2]
      rfl
    exact rescaling_preserves_means _ _ _ _ _ _ _ hL hU
      (s.lower_consistent t k) (s.bounds (t + 1) k).2.1 (s.upper_consistent t k)

/-- Positive history weight and an unresolved interval exclude the source's zero divisor. -/
theorem old_width_pos (t : ℕ) (k : Fin (s.degree (t + 1) + 1))
    (h : s.Past t) (j : Fin (s.degree t + 1))
    (hh : 0 < s.weight t j h) (hj : 0 < s.reverse t k j)
    (hwidth : (s.thresholds t j h).1 < (s.thresholds t j h).2) :
    0 < s.upperBar t k - s.lowerBar t k := by
  have hpos := mean_width_pos (s.weight (t + 1) k)
    (fun z => (s.thresholds t z.2 z.1).1) (fun z => (s.thresholds t z.2 z.1).2)
    (s.weight_nonneg (t + 1) k) (fun z => (s.thresholds_bounds t z.2 z.1).2.1)
    (h, j) (mul_pos hj hh) hwidth
  rw [s.mean_previous t k (fun j h => (s.thresholds t j h).2),
    s.mean_previous t k (fun j h => (s.thresholds t j h).1)] at hpos
  simpa only [lowerBar, upperBar, fun j => (s.thresholds_mean t j).1,
    fun j => (s.thresholds_mean t j).2] using hpos

end Scheme

end

end SampLib.EnvelopeFactory
