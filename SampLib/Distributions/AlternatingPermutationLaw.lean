module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Alternating-uniform paths

A path alternates upward and downward comparisons between successive uniforms.
Its finite-prefix masses form a Volterra series. Geometric tail control identifies
that series with trigonometric solutions of the same integral recurrence.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace SampLib.AlternatingPermutationLaw

noncomputable section

/-- Integrate one allowed upward or downward continuation. -/
def transfer (f : Bool → ℝ → ℝ) (up : Bool) (x : ℝ) : ℝ :=
  if up then ∫ y in x..1, f false y else ∫ y in (0 : ℝ)..x, f true y

/-- Probability of passing the next `n` comparisons, starting from `x`.
`up = true` means that the next uniform must be at least `x`. -/
def pathMass : ℕ → Bool → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, up, x => transfer (pathMass n) up x

@[simp] theorem pathMass_zero (up : Bool) (x : ℝ) : pathMass 0 up x = 1 := rfl

@[simp] theorem pathMass_succ_true (n : ℕ) (x : ℝ) :
    pathMass (n + 1) true x = ∫ y in x..1, pathMass n false y := rfl

@[simp] theorem pathMass_succ_false (n : ℕ) (x : ℝ) :
    pathMass (n + 1) false x = ∫ y in (0 : ℝ)..x, pathMass n true y := rfl

theorem continuous_transfer {f : Bool → ℝ → ℝ}
    (hf : ∀ up, Continuous (f up)) (up : Bool) : Continuous (transfer f up) := by
  cases up
  · exact (intervalIntegral.differentiable_integral_of_continuous (hf true)).continuous
  · change Continuous (fun x => ∫ y in x..1, f false y)
    rw [show (fun x => ∫ y in x..1, f false y) =
        (fun x => -(∫ y in (1 : ℝ)..x, f false y)) from
      funext fun x => intervalIntegral.integral_symm 1 x]
    exact (intervalIntegral.differentiable_integral_of_continuous (hf false)).continuous.neg

/-- Finite path masses are polynomials, hence continuous even outside the sampling interval. -/
theorem continuous_pathMass (n : ℕ) (up : Bool) : Continuous (pathMass n up) := by
  induction n generalizing up with
  | zero => exact continuous_const
  | succ n IH => exact continuous_transfer IH up

theorem measurable_pathMass (n : ℕ) (up : Bool) : Measurable (pathMass n up) :=
  (continuous_pathMass n up).measurable

private theorem transfer_nonneg {f : Bool → ℝ → ℝ}
    (hf : ∀ up x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f up x) (up : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ transfer f up x := by
  cases up
  · apply intervalIntegral.integral_nonneg hx.1
    intro y hy
    exact hf true y ⟨hy.1, hy.2.trans hx.2⟩
  · apply intervalIntegral.integral_nonneg hx.2
    intro y hy
    exact hf false y ⟨hx.1.trans hy.1, hy.2⟩

theorem transfer_norm_le {f : Bool → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ up x, x ∈ Icc (0 : ℝ) 1 → ‖f up x‖ ≤ C) (up : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖transfer f up x‖ ≤ C := by
  cases up
  · change ‖∫ y in (0 : ℝ)..x, f true y‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y (hy : y ∈ uIoc (0 : ℝ) x) => hf true y
        ⟨(show 0 < y from (uIoc_of_le hx.1 ▸ hy).1).le,
          (show y ≤ x from (uIoc_of_le hx.1 ▸ hy).2).trans hx.2⟩)
    apply hb.trans
    rw [sub_zero, abs_of_nonneg hx.1]
    exact mul_le_of_le_one_right hC hx.2
  · change ‖∫ y in x..1, f false y‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y (hy : y ∈ uIoc x 1) => hf false y
        ⟨hx.1.trans (show x < y from (uIoc_of_le hx.2 ▸ hy).1).le,
          (show y ≤ 1 from (uIoc_of_le hx.2 ▸ hy).2)⟩)
    apply hb.trans
    rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
    exact mul_le_of_le_one_right hC (by linarith [hx.1])

theorem pathMass_nonneg (n : ℕ) (up : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ pathMass n up x := by
  induction n generalizing up x with
  | zero => exact zero_le_one
  | succ n IH => exact transfer_nonneg (fun up x hx => IH up hx) up hx

theorem pathMass_norm_le_one (n : ℕ) (up : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖pathMass n up x‖ ≤ 1 := by
  induction n generalizing up x with
  | zero => norm_num
  | succ n IH => exact transfer_norm_le zero_le_one (fun up x hx => IH up hx) up hx

theorem pathMass_bounds (n : ℕ) (up : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ pathMass n up x ∧ pathMass n up x ≤ 1 :=
  ⟨pathMass_nonneg n up hx, (le_abs_self _).trans (pathMass_norm_le_one n up hx)⟩

/-- The empty event and the one-uniform event both have mass one. -/
def eventMass : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∫ x in (0 : ℝ)..1, pathMass n true x

@[simp] theorem eventMass_zero : eventMass 0 = 1 := rfl

@[simp] theorem eventMass_succ (n : ℕ) :
    eventMass (n + 1) = ∫ x in (0 : ℝ)..1, pathMass n true x := rfl

@[simp] theorem eventMass_one : eventMass 1 = 1 := by simp [eventMass]

private theorem integral_lower (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, if y ≤ x then f y else 0) = ∫ y in (0 : ℝ)..x, f y := by
  simpa only [Set.indicator_apply, mem_ofPred_eq] using
    intervalIntegral.integral_indicator (μ := volume) (f := f) hx

private theorem integral_upper (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, if x ≤ y then f y else 0) = ∫ y in x..1, f y := by
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  calc
    _ = ∫ y in (0 : ℝ)..1, if y ≤ 1 - x then f (1 - y) else 0 := by
      have h := intervalIntegral.integral_comp_sub_left
        (fun y => if x ≤ y then f y else 0) (a := 0) (b := 1) 1
      simp only [sub_zero, sub_self] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro y _
      have heq : x ≤ 1 - y ↔ y ≤ 1 - x := by
        constructor <;> intro h <;> linarith
      simp only [heq]
    _ = ∫ y in (0 : ℝ)..(1 - x), f (1 - y) := integral_lower _ hx'
    _ = ∫ y in x..1, f y := by
      rw [intervalIntegral.integral_comp_sub_left]
      congr 1 <;> ring

/-- Surviving a descending comparison restricts the next uniform to `[0,x]`. -/
theorem integral_pathMass_le (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, if y ≤ x then pathMass n true y else 0) =
      pathMass (n + 1) false x := integral_lower _ hx

/-- Surviving an ascending comparison restricts the next uniform to `[x,1]`. -/
theorem integral_pathMass_ge (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, if x ≤ y then pathMass n false y else 0) =
      pathMass (n + 1) true x := integral_upper _ hx

/-- Reflecting every uniform swaps upward and downward comparisons. -/
theorem pathMass_reflect (n : ℕ) (up : Bool) (x : ℝ) :
    pathMass n (!up) (1 - x) = pathMass n up x := by
  induction n generalizing up x with
  | zero => rfl
  | succ n IH =>
    cases up
    · simp only [Bool.not_false, pathMass_succ_true, pathMass_succ_false]
      calc
        _ = ∫ y in (1 - x)..1, pathMass n true (1 - y) := by
          apply intervalIntegral.integral_congr
          intro y _
          exact (IH false y).symm
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left]
          congr 1 <;> ring
    · simp only [Bool.not_true, pathMass_succ_false, pathMass_succ_true]
      calc
        _ = ∫ y in (0 : ℝ)..(1 - x), pathMass n false (1 - y) := by
          apply intervalIntegral.integral_congr
          intro y _
          exact (IH true y).symm
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left]
          congr 1 <;> ring

/-- The initial uniform integrates either reflected orientation with the same mass. -/
theorem eventMass_eq_pathMass_zero (n : ℕ) : eventMass n = pathMass n true 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    change (∫ x in (0 : ℝ)..1, pathMass n true x) =
      ∫ x in (0 : ℝ)..1, pathMass n false x
    calc
      _ = ∫ x in (0 : ℝ)..1, pathMass n false (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact (pathMass_reflect n true x).symm
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left]; norm_num

theorem eventMass_bounds (n : ℕ) : 0 ≤ eventMass n ∧ eventMass n ≤ 1 := by
  rw [eventMass_eq_pathMass_zero]
  exact pathMass_bounds n true (by norm_num)

end

end SampLib.AlternatingPermutationLaw
