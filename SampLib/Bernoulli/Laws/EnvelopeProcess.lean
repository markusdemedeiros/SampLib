import SampLib.Bernoulli.Laws.EnvelopeCoefficients
import SampLib.Bernoulli.Laws.EnvelopeFuture
import SampLib.Bernoulli.Support.BinomialFinite

/-! # Forward binomial steps on the reverse-conditioned shadow histories -/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.EnvelopeFactory.Coefficients

noncomputable section

variable (a : Coefficients)

abbrev State (t : ℕ) := Fin (a.degree t + 1) × a.toScheme.Past t
abbrev Branch (t : ℕ) := Fin (a.degree (t + 1) - a.degree t + 1)

def advance (t : ℕ) (x : a.State t) (d : a.Branch t) : a.State (t + 1) :=
  (⟨(x.1 : ℕ) + d, by
    have hx := x.1.isLt
    have hd := d.isLt
    have hg := a.grows t
    omega⟩, (x.2, x.1))

def process (p : unitInterval) : IntervalProcess a.State a.Branch where
  weight t d := BinomialFinite.pmf p (a.degree (t + 1) - a.degree t) d
  weight_sum t := BinomialFinite.pmf_sum p _
  next := a.advance
  lower t x := (a.toScheme.thresholds t x.1 x.2).1
  upper t x := (a.toScheme.thresholds t x.1 x.2).2
  ordered t x := (a.toScheme.thresholds_bounds t x.1 x.2).2.1
  nested t x d := by
    have h := a.toScheme.thresholds_nested t (a.advance t x d).1 x.2 x.1
    exact ⟨h.1, h.2.2⟩

/-- Conditional history weights are genuine finite probabilities. -/
theorem conditionalWeight_sum (t : ℕ) (k : Fin (a.degree t + 1)) :
    (∑ h, ENNReal.ofReal (a.toScheme.weight t k h)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => a.toScheme.weight_nonneg t k h),
    a.toScheme.weight_sum]
  exact ENNReal.ofReal_one

/-- The reverse-conditioned representation of the complete state law. -/
def stateMass (p : unitInterval) (t : ℕ) (x : a.State t) : ℝ≥0∞ :=
  BinomialFinite.pmf p (a.degree t) x.1 * ENNReal.ofReal (a.toScheme.weight t x.1 x.2)

theorem stateMass_sum (p : unitInterval) (t : ℕ) : ∑ x, a.stateMass p t x = 1 := by
  simp only [State, stateMass, Fintype.sum_prod_type]
  simp only [← mul_sum, a.conditionalWeight_sum, mul_one, BinomialFinite.pmf_sum]

/-- The unique initial state has no observations and the full uniform interval. -/
def initial : a.State 0 :=
  (⟨0, by omega⟩, ())

theorem initial_bounds (p : unitInterval) :
    (a.process p).lower 0 a.initial = 0 ∧ (a.process p).upper 0 a.initial = 1 :=
  ⟨rfl, rfl⟩

theorem advance_positive (t : ℕ) (x : a.State t) (d : a.Branch t)
    (hx : 0 < a.toScheme.weight t x.1 x.2) :
    0 < a.toScheme.weight (t + 1) (a.advance t x d).1 (a.advance t x d).2 := by
  apply mul_pos ?_ hx
  change 0 < (ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1))
    ((x.1 : ℕ) + d) x.1 : ℝ)
  exact_mod_cast ReverseBinomial.coefficient_pos (a.degree t) (a.degree (t + 1))
    ((x.1 : ℕ) + d) x.1 (by
      have hx := x.1.isLt
      have hd := d.isLt
      have hg := a.grows t
      omega)
    (by omega) (by have h := x.1.isLt; omega) (by have h := d.isLt; omega)

end

end SampLib.EnvelopeFactory.Coefficients
