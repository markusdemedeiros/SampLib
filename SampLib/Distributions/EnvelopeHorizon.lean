import SampLib.Distributions.EnvelopeMoments

/-! # Initial credit and termination of the general envelope factory

Forward binomial transport identifies every finite shadow horizon. Resolved
credits increase, so monotone convergence identifies their supremum even when a
null outcome has infinite payoff. Only the unresolved probability is paid as an
extra unit credit; its Bernstein mean tends to zero.
-/

open Finset Filter MeasureTheory
open scoped ENNReal Topology

namespace SampLib.EnvelopeFactory

noncomputable section

namespace Coefficients

variable (a : Coefficients)

theorem initial_average (p : unitInterval) (H : a.State 0 → ℝ≥0∞) :
    a.average p 0 H = H a.initial := by
  have hs : Subsingleton (a.State 0) := by
    change Subsingleton (Fin (a.degree 0 + 1) × Unit)
    rw [a.initial_degree]
    refine ⟨?_⟩
    intro x y
    apply Prod.ext
    · apply Fin.ext
      have hx := x.1.isLt
      have hy := y.1.isLt
      omega
    · exact Subsingleton.elim _ _
  unfold average
  calc
    _ = (∑ x, a.stateMass p 0 x) * H a.initial := by
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      rw [@Subsingleton.elim _ hs x a.initial]
    _ = _ := by rw [a.stateMass_sum, one_mul]

def resolvedAverage (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ) : ℝ≥0∞ :=
  a.average p t (fun x =>
    ∫⁻ u, (a.process p).resolvedFuture F N t x u ∂DyadicPosterior.unitLaw)

def debtAverage (p : unitInterval) (N t : ℕ) : ℝ≥0∞ :=
  a.average p t (fun x =>
    ∫⁻ u, (a.process p).unresolvedFuture N t x u ∂DyadicPosterior.unitLaw)

theorem resolvedAverage_succ (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ) :
    a.resolvedAverage p F (N + 1) t = a.resolvedAverage p F N (t + 1) := by
  unfold resolvedAverage average
  simp_rw [(a.process p).integral_resolvedFuture_succ]
  exact a.stateMass_transport p t (fun x =>
    ∫⁻ u, (a.process p).resolvedFuture F N (t + 1) x u ∂DyadicPosterior.unitLaw)

theorem debtAverage_succ (p : unitInterval) (N t : ℕ) :
    a.debtAverage p (N + 1) t = a.debtAverage p N (t + 1) := by
  unfold debtAverage average
  simp_rw [(a.process p).integral_unresolvedFuture_succ]
  exact a.stateMass_transport p t (fun x =>
    ∫⁻ u, (a.process p).unresolvedFuture N (t + 1) x u ∂DyadicPosterior.unitLaw)

theorem resolvedAverage_zero (p : unitInterval) (F : Bool → ℝ≥0∞) (t : ℕ) :
    a.resolvedAverage p F 0 t = ENNReal.ofReal (a.lowerMean t p) * F true +
      ENNReal.ofReal (1 - a.upperMean t p) * F false := by
  have hpoint (x : a.State t) :
      (∫⁻ u, (a.process p).resolvedFuture F 0 t x u ∂DyadicPosterior.unitLaw) =
        ENNReal.ofReal (a.toScheme.thresholds t x.1 x.2).1 * F true +
          ENNReal.ofReal (1 - (a.toScheme.thresholds t x.1 x.2).2) * F false :=
    integral_resolvedCredit _ _ (a.toScheme.thresholds_bounds t x.1 x.2).1
      (a.toScheme.thresholds_bounds t x.1 x.2).2.1
      (a.toScheme.thresholds_bounds t x.1 x.2).2.2 F
  unfold resolvedAverage average
  simp_rw [hpoint]
  simp only [mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul]
  change a.average p t (fun x => ENNReal.ofReal (a.toScheme.thresholds t x.1 x.2).1) *
    F true + a.average p t (fun x => ENNReal.ofReal
      (1 - (a.toScheme.thresholds t x.1 x.2).2)) * F false = _
  rw [a.lower_moment, a.failure_moment]

theorem debtAverage_zero (p : unitInterval) (t : ℕ) :
    a.debtAverage p 0 t = ENNReal.ofReal (a.upperMean t p - a.lowerMean t p) := by
  have hpoint (x : a.State t) :
      (∫⁻ u, (a.process p).unresolvedFuture 0 t x u ∂DyadicPosterior.unitLaw) =
        ENNReal.ofReal ((a.toScheme.thresholds t x.1 x.2).2 -
          (a.toScheme.thresholds t x.1 x.2).1) :=
    integral_unresolvedIndicator _ _ (a.toScheme.thresholds_bounds t x.1 x.2).1
      (a.toScheme.thresholds_bounds t x.1 x.2).2.2
  unfold debtAverage
  simp_rw [hpoint]
  exact a.width_moment p t

theorem resolvedAverage_eq (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ) :
    a.resolvedAverage p F N t = ENNReal.ofReal (a.lowerMean (t + N) p) * F true +
      ENNReal.ofReal (1 - a.upperMean (t + N) p) * F false := by
  induction N generalizing t with
  | zero => simpa only [Nat.add_zero] using a.resolvedAverage_zero p F t
  | succ N IH =>
    rw [a.resolvedAverage_succ, IH, show t + 1 + N = t + (N + 1) by omega]

theorem debtAverage_eq (p : unitInterval) (N t : ℕ) :
    a.debtAverage p N t = ENNReal.ofReal (a.upperMean (t + N) p - a.lowerMean (t + N) p) := by
  induction N generalizing t with
  | zero => simpa only [Nat.add_zero] using a.debtAverage_zero p t
  | succ N IH =>
    rw [a.debtAverage_succ, IH, show t + 1 + N = t + (N + 1) by omega]

theorem initial_resolvedFuture (p : unitInterval) (F : Bool → ℝ≥0∞) (N : ℕ) :
    (∫⁻ u, (a.process p).resolvedFuture F N 0 a.initial u ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (a.lowerMean N p) * F true +
        ENNReal.ofReal (1 - a.upperMean N p) * F false := by
  have h := a.resolvedAverage_eq p F N 0
  rw [resolvedAverage, a.initial_average] at h
  simpa only [Nat.zero_add] using h

theorem initial_unresolvedFuture (p : unitInterval) (N : ℕ) :
    (∫⁻ u, (a.process p).unresolvedFuture N 0 a.initial u ∂DyadicPosterior.unitLaw) =
      ENNReal.ofReal (a.upperMean N p - a.lowerMean N p) := by
  have h := a.debtAverage_eq p N 0
  rw [debtAverage, a.initial_average] at h
  simpa only [Nat.zero_add] using h

theorem lowerMass_monotone (p : unitInterval) :
    Monotone (fun N => ENNReal.ofReal (a.lowerMean N p)) := by
  intro i j hij
  have h := lintegral_mono (μ := DyadicPosterior.unitLaw) (fun u =>
    (a.process p).resolvedFuture_mono (fun b => if b then 1 else 0) 0 a.initial u hij)
  rw [a.initial_resolvedFuture, a.initial_resolvedFuture] at h
  simpa using h

theorem failureMass_monotone (p : unitInterval) :
    Monotone (fun N => ENNReal.ofReal (1 - a.upperMean N p)) := by
  intro i j hij
  have h := lintegral_mono (μ := DyadicPosterior.unitLaw) (fun u =>
    (a.process p).resolvedFuture_mono (fun b => if b then 0 else 1) 0 a.initial u hij)
  rw [a.initial_resolvedFuture, a.initial_resolvedFuture] at h
  simpa using h

end Coefficients

namespace Parameters

variable {p : unitInterval} (a : Parameters p)

theorem lowerMass_iSup :
    (⨆ N, ENNReal.ofReal (a.toCoefficients.lowerMean N p)) = ENNReal.ofReal (a.target : ℝ) := by
  apply tendsto_nhds_unique (tendsto_atTop_iSup (a.toCoefficients.lowerMass_monotone p))
  exact (ENNReal.continuous_ofReal.tendsto _).comp a.lower_converges

theorem failureMass_iSup :
    (⨆ N, ENNReal.ofReal (1 - a.toCoefficients.upperMean N p)) =
      ENNReal.ofReal (1 - (a.target : ℝ)) := by
  apply tendsto_nhds_unique (tendsto_atTop_iSup (a.toCoefficients.failureMass_monotone p))
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_const_nhds.sub a.upper_converges)

/-- Multiplication commutes with monotone suprema, including `0 * ∞ = 0`. -/
theorem limit_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ u, (a.toCoefficients.process p).limitCredit F 0 a.toCoefficients.initial u
      ∂DyadicPosterior.unitLaw) = RealCoin.credit a.target F := by
  rw [IntervalProcess.integral_limitCredit]
  simp_rw [a.toCoefficients.initial_resolvedFuture]
  rw [← ENNReal.iSup_add_iSup_of_monotone
    ((a.toCoefficients.lowerMass_monotone p).mul_const' (F true))
    ((a.toCoefficients.failureMass_monotone p).mul_const' (F false)),
    ← ENNReal.iSup_mul, ← ENNReal.iSup_mul, a.lowerMass_iSup, a.failureMass_iSup]
  rfl

theorem horizon_expectation (F : Bool → ℝ≥0∞) (N : ℕ) :
    (∫⁻ u, (a.toCoefficients.process p).horizonCredit F N 0 a.toCoefficients.initial u
      ∂DyadicPosterior.unitLaw) = RealCoin.credit a.target F +
        ENNReal.ofReal (a.toCoefficients.upperMean N p - a.toCoefficients.lowerMean N p) := by
  change (∫⁻ u, (a.toCoefficients.process p).limitCredit F 0 a.toCoefficients.initial u +
    (a.toCoefficients.process p).unresolvedFuture N 0 a.toCoefficients.initial u
      ∂DyadicPosterior.unitLaw) = _
  rw [lintegral_add_left
    ((a.toCoefficients.process p).measurable_limitCredit F 0 a.toCoefficients.initial) _,
    a.limit_expectation, a.toCoefficients.initial_unresolvedFuture]

theorem exists_horizon (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, (∫⁻ u, (a.toCoefficients.process p).horizonCredit F N 0 a.toCoefficients.initial u
      ∂DyadicPosterior.unitLaw) ≤ RealCoin.credit a.target F + δ := by
  have ht : Tendsto (fun N => ENNReal.ofReal
      (a.toCoefficients.upperMean N p - a.toCoefficients.lowerMean N p)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp a.width_vanishes
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  exact ⟨N, by rw [a.horizon_expectation]; exact add_le_add le_rfl hN.le⟩

end Parameters

end

end SampLib.EnvelopeFactory
