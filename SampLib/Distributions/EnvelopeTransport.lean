import SampLib.Distributions.EnvelopeProcess
import SampLib.Distributions.ReverseBinomialFinite

/-! # Forward/reverse transport of complete envelope histories

The reverse law is not merely a marginal identity: it transports every joint
history credit. The finite hypergeometric disintegration remains valid for
infinite credits and deterministic endpoint coins.
-/

open Finset
open scoped ENNReal

namespace SampLib.BinomialFinite

theorem pmf_eq_singleton (p : unitInterval) (n : ℕ) (k : Fin (n + 1)) :
    pmf p n k = ProbabilityTheory.binomial n p {(k : ℕ)} :=
  (ProbabilityTheory.binomial_singleton n k p).symm

end SampLib.BinomialFinite

namespace SampLib.EnvelopeFactory.Coefficients

noncomputable section

variable (a : Coefficients)

/-- One actual fresh-binomial block gives precisely the next reverse-conditioned state law. -/
theorem stateMass_transport (p : unitInterval) (t : ℕ) (G : a.State (t + 1) → ℝ≥0∞) :
    (∑ x : a.State t, a.stateMass p t x *
      ∑ d : a.Branch t, BinomialFinite.pmf p (a.degree (t + 1) - a.degree t) d *
        G (a.advance t x d)) =
      ∑ y : a.State (t + 1), a.stateMass p (t + 1) y * G y := by
  let jointCredit (j : Fin (a.degree t + 1)) (k : Fin (a.degree (t + 1) + 1)) :=
    ∑ h : a.toScheme.Past t, ENNReal.ofReal (a.toScheme.weight t j h) * G (k, (h, j))
  have hjoint := ReverseBinomial.expectation_joint_fin (a.degree t) (a.degree (t + 1))
    (a.grows t).le p jointCredit
  calc
    _ = ∑ j : Fin (a.degree t + 1), BinomialFinite.pmf p (a.degree t) j *
        ∑ d : a.Branch t, BinomialFinite.pmf p (a.degree (t + 1) - a.degree t) d *
          jointCredit j (ReverseBinomial.totalCount (a.grows t).le j d) := by
      simp only [State, stateMass, Fintype.sum_prod_type, jointCredit, mul_sum]
      apply sum_congr rfl
      intro j _
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro h _
      simp only [advance, ReverseBinomial.totalCount]
      ring
    _ = ∑ k : Fin (a.degree (t + 1) + 1), BinomialFinite.pmf p (a.degree (t + 1)) k *
        ∑ j : Fin (a.degree t + 1),
          ReverseBinomial.weight (a.degree t) (a.degree (t + 1)) k j * jointCredit j k := by
      simpa only [← BinomialFinite.pmf_eq_singleton] using hjoint
    _ = _ := by
      simp only [State, stateMass, Fintype.sum_prod_type, jointCredit, mul_sum]
      apply sum_congr rfl
      intro k _
      rw [sum_comm]
      apply sum_congr rfl
      intro h _
      apply sum_congr rfl
      intro j _
      simp only [Scheme.weight]
      rw [ENNReal.ofReal_mul (a.toScheme.reverse_nonneg t k j)]
      change _ = _ * (ReverseBinomial.weight _ _ _ _ * _) * _
      ring

end

end SampLib.EnvelopeFactory.Coefficients
