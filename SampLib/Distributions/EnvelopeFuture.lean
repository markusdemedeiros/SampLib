module

public import SampLib.Distributions.EnvelopeRescaling
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! # Limit credits and finite-horizon debt for nested random intervals

Resolved credits increase with the horizon. Their supremum therefore handles
infinite continuation credits without multiplying infinity by a vanishing error.
Only an unresolved indicator is added to finance finite proof truncation.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.EnvelopeFactory

noncomputable section

/-- A finite-branching interval process; the state may retain its entire history. -/
structure IntervalProcess (State Branch : ℕ → Type) [∀ t, Fintype (Branch t)] where
  weight : (t : ℕ) → Branch t → ℝ≥0∞
  weight_sum : ∀ t, ∑ b, weight t b = 1
  next : (t : ℕ) → State t → Branch t → State (t + 1)
  lower : (t : ℕ) → State t → ℝ
  upper : (t : ℕ) → State t → ℝ
  ordered : ∀ t x, lower t x ≤ upper t x
  nested : ∀ t x b, lower t x ≤ lower (t + 1) (next t x b) ∧
    upper (t + 1) (next t x b) ≤ upper t x

def resolvedCredit (L U u : ℝ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  if u < L then F true else if u < U then 0 else F false

def unresolvedIndicator (L U u : ℝ) : ℝ≥0∞ := if L ≤ u ∧ u < U then 1 else 0

theorem resolvedCredit_mono (L U L' U' u : ℝ) (F : Bool → ℝ≥0∞)
    (hLL : L ≤ L') (hLU : L' ≤ U') (hUU : U' ≤ U) :
    resolvedCredit L U u F ≤ resolvedCredit L' U' u F := by
  by_cases hlo : u < L
  · simp [resolvedCredit, hlo, hlo.trans_le hLL]
  · by_cases hhi : u < U
    · simp only [resolvedCredit, hlo, ite_false, hhi, ite_true]
      exact bot_le
    · have hU : U ≤ u := le_of_not_gt hhi
      have hU' : ¬u < U' := not_lt.mpr (hUU.trans hU)
      have hL' : ¬u < L' := not_lt.mpr (hLU.trans (hUU.trans hU))
      simp [resolvedCredit, hlo, hhi, hL', hU']

theorem measurable_resolvedCredit (L U : ℝ) (F : Bool → ℝ≥0∞) :
    Measurable (fun u => resolvedCredit L U u F) :=
  Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem measurable_unresolvedIndicator (L U : ℝ) :
    Measurable (unresolvedIndicator L U) :=
  Measurable.ite measurableSet_Ico measurable_const measurable_const

namespace IntervalProcess

variable {State Branch : ℕ → Type} [∀ t, Fintype (Branch t)]
variable (P : IntervalProcess State Branch)

def resolvedFuture (P : IntervalProcess State Branch) (F : Bool → ℝ≥0∞) :
    (N t : ℕ) → State t → ℝ → ℝ≥0∞
  | 0, t, x, u => resolvedCredit (P.lower t x) (P.upper t x) u F
  | N + 1, t, x, u =>
      ∑ b, P.weight t b * resolvedFuture P F N (t + 1) (P.next t x b) u

def unresolvedFuture (P : IntervalProcess State Branch) : (N t : ℕ) → State t → ℝ → ℝ≥0∞
  | 0, t, x, u => unresolvedIndicator (P.lower t x) (P.upper t x) u
  | N + 1, t, x, u => ∑ b, P.weight t b * unresolvedFuture P N (t + 1) (P.next t x b) u

theorem measurable_resolvedFuture (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) :
    Measurable (P.resolvedFuture F N t x) := by
  induction N generalizing t with
  | zero => exact measurable_resolvedCredit _ _ F
  | succ N IH =>
    exact Finset.measurable_fun_sum _ (fun b _ =>
      measurable_const.mul (IH (t + 1) (P.next t x b)))

theorem measurable_unresolvedFuture (N t : ℕ) (x : State t) :
    Measurable (P.unresolvedFuture N t x) := by
  induction N generalizing t with
  | zero => exact measurable_unresolvedIndicator _ _
  | succ N IH =>
    exact Finset.measurable_fun_sum _ (fun b _ =>
      measurable_const.mul (IH (t + 1) (P.next t x b)))

theorem integral_resolvedFuture_succ (μ : Measure ℝ) (F : Bool → ℝ≥0∞)
    (N t : ℕ) (x : State t) :
    (∫⁻ u, P.resolvedFuture F (N + 1) t x u ∂μ) =
      ∑ b, P.weight t b * ∫⁻ u, P.resolvedFuture F N (t + 1) (P.next t x b) u ∂μ := by
  change (∫⁻ u, ∑ b, P.weight t b *
    P.resolvedFuture F N (t + 1) (P.next t x b) u ∂μ) = _
  rw [lintegral_finsetSum (f := fun b u =>
    P.weight t b * P.resolvedFuture F N (t + 1) (P.next t x b) u) univ (fun b _ =>
      measurable_const.mul (P.measurable_resolvedFuture F N (t + 1) (P.next t x b)))]
  apply sum_congr rfl
  intro b _
  exact lintegral_const_mul _ (P.measurable_resolvedFuture F N (t + 1) (P.next t x b))

theorem integral_unresolvedFuture_succ (μ : Measure ℝ) (N t : ℕ) (x : State t) :
    (∫⁻ u, P.unresolvedFuture (N + 1) t x u ∂μ) =
      ∑ b, P.weight t b * ∫⁻ u, P.unresolvedFuture N (t + 1) (P.next t x b) u ∂μ := by
  change (∫⁻ u, ∑ b, P.weight t b *
    P.unresolvedFuture N (t + 1) (P.next t x b) u ∂μ) = _
  rw [lintegral_finsetSum (f := fun b u =>
    P.weight t b * P.unresolvedFuture N (t + 1) (P.next t x b) u) univ (fun b _ =>
      measurable_const.mul (P.measurable_unresolvedFuture N (t + 1) (P.next t x b)))]
  apply sum_congr rfl
  intro b _
  exact lintegral_const_mul _ (P.measurable_unresolvedFuture N (t + 1) (P.next t x b))

/-- Monotone resolved credits retain zero-probability infinite payoffs exactly. -/
theorem resolvedFuture_le_succ (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) (u : ℝ) :
    P.resolvedFuture F N t x u ≤ P.resolvedFuture F (N + 1) t x u := by
  induction N generalizing t with
  | zero =>
    change resolvedCredit _ _ u F ≤ ∑ b, P.weight t b * resolvedCredit _ _ u F
    calc
      _ = (∑ b, P.weight t b) * resolvedCredit (P.lower t x) (P.upper t x) u F := by
        rw [P.weight_sum, one_mul]
      _ = ∑ b, P.weight t b * resolvedCredit (P.lower t x) (P.upper t x) u F := by rw [sum_mul]
      _ ≤ _ := by
        apply sum_le_sum
        intro b _
        apply mul_le_mul_right
        exact resolvedCredit_mono _ _ _ _ u F (P.nested t x b).1
          (P.ordered (t + 1) (P.next t x b)) (P.nested t x b).2
  | succ N IH =>
    apply sum_le_sum
    intro b _
    exact mul_le_mul_right (IH (t + 1) (P.next t x b)) _

theorem resolvedFuture_mono (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) (u : ℝ) :
    Monotone (fun N => P.resolvedFuture F N t x u) :=
  monotone_nat_of_le_succ (fun N => P.resolvedFuture_le_succ F N t x u)

def limitCredit (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) (u : ℝ) : ℝ≥0∞ :=
  ⨆ N, P.resolvedFuture F N t x u

theorem measurable_limitCredit (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) :
    Measurable (P.limitCredit F t x) :=
  Measurable.iSup (fun N => P.measurable_resolvedFuture F N t x)

theorem resolved_le_limitCredit (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) (u : ℝ) :
    resolvedCredit (P.lower t x) (P.upper t x) u F ≤ P.limitCredit F t x u :=
  le_iSup (fun N => P.resolvedFuture F N t x u) 0

/-- The supremum commutes with the next finite probability kernel. -/
theorem limitCredit_step (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) (u : ℝ) :
    P.limitCredit F t x u =
      ∑ b, P.weight t b * P.limitCredit F (t + 1) (P.next t x b) u := by
  apply le_antisymm
  · apply iSup_le
    intro N
    cases N with
    | zero =>
      apply (P.resolvedFuture_le_succ F 0 t x u).trans
      apply sum_le_sum
      intro b _
      exact mul_le_mul_right (le_iSup (fun N =>
        P.resolvedFuture F N (t + 1) (P.next t x b) u) 0) _
    | succ N =>
      apply sum_le_sum
      intro b _
      exact mul_le_mul_right (le_iSup (fun N =>
        P.resolvedFuture F N (t + 1) (P.next t x b) u) N) _
  · simp only [limitCredit, ENNReal.mul_iSup]
    rw [ENNReal.finsetSum_iSup_of_monotone (fun b =>
      (P.resolvedFuture_mono F (t + 1) (P.next t x b) u).const_mul' (P.weight t b))]
    apply iSup_le
    intro N
    exact le_iSup (fun N => P.resolvedFuture F N t x u) (N + 1)

def horizonCredit (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) (u : ℝ) : ℝ≥0∞ :=
  P.limitCredit F t x u + P.unresolvedFuture N t x u

theorem measurable_horizonCredit (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) :
    Measurable (P.horizonCredit F N t x) :=
  (P.measurable_limitCredit F t x).add (P.measurable_unresolvedFuture N t x)

theorem horizonCredit_step (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) (u : ℝ) :
    P.horizonCredit F (N + 1) t x u =
      ∑ b, P.weight t b * P.horizonCredit F N (t + 1) (P.next t x b) u := by
  rw [horizonCredit, P.limitCredit_step]
  simp only [unresolvedFuture, horizonCredit, mul_add, sum_add_distrib]

/-- Integrating the one-step identity preserves every posterior on the cached uniform. -/
theorem horizon_expectation (μ : Measure ℝ) (F : Bool → ℝ≥0∞)
    (N t : ℕ) (x : State t) :
    (∑ b, P.weight t b *
      ∫⁻ u, P.horizonCredit F N (t + 1) (P.next t x b) u ∂μ) =
        ∫⁻ u, P.horizonCredit F (N + 1) t x u ∂μ := by
  simp_rw [P.horizonCredit_step F N t x]
  rw [lintegral_finsetSum (f := fun b u =>
    P.weight t b * P.horizonCredit F N (t + 1) (P.next t x b) u) univ (fun b _ =>
      measurable_const.mul (P.measurable_horizonCredit F N (t + 1) (P.next t x b)))]
  apply sum_congr rfl
  intro b _
  exact (lintegral_const_mul _
    (P.measurable_horizonCredit F N (t + 1) (P.next t x b))).symm

/-- Monotone convergence applies to resolved credits, including infinite payoffs. -/
theorem integral_limitCredit (μ : Measure ℝ) (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) :
    (∫⁻ u, P.limitCredit F t x u ∂μ) =
      ⨆ N, ∫⁻ u, P.resolvedFuture F N t x u ∂μ := by
  apply lintegral_iSup (fun N => P.measurable_resolvedFuture F N t x)
  intro i j hij u
  exact P.resolvedFuture_mono F t x u hij

theorem lower_credit (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) (u : ℝ)
    (hu : u < P.lower t x) : F true ≤ P.horizonCredit F N t x u := by
  apply le_trans ?_ (le_add_right le_rfl)
  have h := P.resolved_le_limitCredit F t x u
  simpa only [resolvedCredit, hu, ite_true] using h

theorem upper_credit (F : Bool → ℝ≥0∞) (N t : ℕ) (x : State t) (u : ℝ)
    (hu : P.upper t x ≤ u) : F false ≤ P.horizonCredit F N t x u := by
  apply le_trans ?_ (le_add_right le_rfl)
  have hlo : ¬u < P.lower t x := not_lt.mpr ((P.ordered t x).trans hu)
  have hhi : ¬u < P.upper t x := not_lt.mpr hu
  have h := P.resolved_le_limitCredit F t x u
  simpa only [resolvedCredit, hlo, hhi, ite_false] using h

/-- At the proof horizon, the unresolved indicator itself supplies the contradictory unit credit. -/
theorem unresolved_credit (F : Bool → ℝ≥0∞) (t : ℕ) (x : State t) (u : ℝ)
    (hu : P.lower t x ≤ u ∧ u < P.upper t x) : 1 ≤ P.horizonCredit F 0 t x u := by
  simp only [horizonCredit, unresolvedFuture, unresolvedIndicator, hu]
  exact le_add_left le_rfl

end IntervalProcess

end

end SampLib.EnvelopeFactory
