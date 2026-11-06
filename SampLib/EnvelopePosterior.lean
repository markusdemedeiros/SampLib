import SampLib.Distributions.EnvelopeHorizon
import SampLib.EnvelopeRealization
import SampLib.Distributions.BoundsKernel

/-! # Conditional envelope credits for one owned cached uniform

Posterior refinement preserves a joint history/uniform kernel. The two observed
comparisons justify returning, while an unresolved comparison supplies the
strict width needed by the source's exact rational division.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.EnvelopeFactory

noncomputable section

namespace Coefficients

variable (a : Coefficients)

abbrev credit (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ) (x : a.State t)
    (q : List Bool) : ℝ≥0∞ :=
  DyadicPosterior.credit q ((a.process p).horizonCredit F N t x)

theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ)
    (x : a.State t) (q : List Bool) :
    (∑ d, BinomialFinite.pmf p (a.degree (t + 1) - a.degree t) d *
      a.credit p F N (t + 1) (a.advance t x d) q) = a.credit p F (N + 1) t x q := by
  unfold credit DyadicPosterior.credit
  exact (a.process p).horizon_expectation (DyadicPosterior.law q) F N t x

theorem lower_credit (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ)
    (x : a.State t) (q : List Bool)
    (hlo : DyadicPosterior.resolves q ((a.process p).lower t x) true) :
    F true ≤ a.credit p F N t x q := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo] with u hu
  exact (a.process p).lower_credit F N t x u (of_decide_eq_true hu)

theorem upper_credit (p : unitInterval) (F : Bool → ℝ≥0∞) (N t : ℕ)
    (x : a.State t) (q : List Bool)
    (hhi : DyadicPosterior.resolves q ((a.process p).upper t x) false) :
    F false ≤ a.credit p F N t x q := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hhi] with u hu
  exact (a.process p).upper_credit F N t x u (le_of_not_gt (of_decide_eq_false hu))

theorem unresolved_credit (p : unitInterval) (F : Bool → ℝ≥0∞) (t : ℕ)
    (x : a.State t) (q : List Bool)
    (hlo : DyadicPosterior.resolves q ((a.process p).lower t x) false)
    (hhi : DyadicPosterior.resolves q ((a.process p).upper t x) true) :
    1 ≤ a.credit p F 0 t x q := by
  apply DyadicPosterior.le_credit_of_ae
  filter_upwards [hlo, hhi] with u hu₀ hu₁
  exact (a.process p).unresolved_credit F t x u
    ⟨le_of_not_gt (of_decide_eq_false hu₀), of_decide_eq_true hu₁⟩

/-- A normalized nonempty posterior cannot resolve an empty interval as unresolved. -/
theorem unresolved_width (q : List Bool) (L U : ℝ)
    (hlo : DyadicPosterior.resolves q L false) (hhi : DyadicPosterior.resolves q U true) :
    L < U := by
  have h : ∀ᵐ u ∂DyadicPosterior.law q, L ≤ u ∧ u < U := by
    filter_upwards [hlo, hhi] with u hu₀ hu₁
    exact ⟨le_of_not_gt (of_decide_eq_false hu₀), of_decide_eq_true hu₁⟩
  obtain ⟨u, hu⟩ := h.exists
  exact hu.1.trans_lt hu.2

/-- The actual fresh count has positive reverse weight, even at input probabilities zero or one. -/
theorem oldWidth_positive (p : unitInterval) (t : ℕ) (x : a.State t) (d : a.Branch t)
    (q : List Bool) (hx : 0 < a.toScheme.weight t x.1 x.2)
    (hlo : DyadicPosterior.resolves q ((a.process p).lower t x) false)
    (hhi : DyadicPosterior.resolves q ((a.process p).upper t x) true) :
    0 < a.upperBarQ t (a.advance t x d).1 - a.lowerBarQ t (a.advance t x d).1 := by
  have hwidth := unresolved_width q _ _ hlo hhi
  change (a.toScheme.thresholds t x.1 x.2).1 <
    (a.toScheme.thresholds t x.1 x.2).2 at hwidth
  rw [← (a.thresholdsQ_coe t x.1 x.2).1, ← (a.thresholdsQ_coe t x.1 x.2).2] at hwidth
  have hq : (a.thresholdsQ t x.1 x.2).1 < (a.thresholdsQ t x.1 x.2).2 := by
    exact_mod_cast hwidth
  have hnext := a.advance_positive t x d hx
  change 0 < a.toScheme.reverse t (a.advance t x d).1 x.1 *
    a.toScheme.weight t x.1 x.2 at hnext
  exact a.oldWidthQ_pos t (a.advance t x d).1 x.2 x.1 hx
    (pos_of_mul_pos_left hnext hx.le) hq

end Coefficients

namespace Parameters

variable {p : unitInterval} (a : Parameters p)

theorem initial_credit (F : Bool → ℝ≥0∞) (N : ℕ) :
    a.toCoefficients.credit p F N 0 a.toCoefficients.initial [] =
      RealCoin.credit a.target F + ENNReal.ofReal
        (a.toCoefficients.upperMean N p - a.toCoefficients.lowerMean N p) := by
  unfold Coefficients.credit DyadicPosterior.credit
  rw [DyadicPosterior.law_nil]
  exact a.horizon_expectation F N

theorem exists_credit_horizon (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, a.toCoefficients.credit p F N 0 a.toCoefficients.initial [] ≤
      RealCoin.credit a.target F + δ := by
  simpa only [Coefficients.credit, DyadicPosterior.credit, DyadicPosterior.law_nil] using
    a.exists_horizon F δ hδ

end Parameters

end

end SampLib.EnvelopeFactory
