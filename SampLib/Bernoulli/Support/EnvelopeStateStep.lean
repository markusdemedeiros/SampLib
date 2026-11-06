import SampLib.Bernoulli.Support.EnvelopeRescaleStep
import SampLib.Bernoulli.Support.EnvelopeState

/-! # The rational source rescaling is the next shadow-history state -/

namespace SampLib.EnvelopeFactory.Coefficients.Realization

open FactoryFractions

noncomputable section

variable {a : Coefficients} (r : a.Realization)

theorem rescaled_state (t : ℕ) (x : a.State t) (d : a.Branch t) :
    rescaledLower (a.stateLower t x) (a.stateUpper t x)
      (r.raw (t + 1) (a.advance t x d).1 false)
      (.ofRat (a.lowerBarQ t (a.advance t x d).1))
      (.ofRat (a.upperBarQ t (a.advance t x d).1)) =
        a.stateLower (t + 1) (a.advance t x d) ∧
    rescaledUpper (a.stateLower t x) (a.stateUpper t x)
      (r.raw (t + 1) (a.advance t x d).1 true)
      (.ofRat (a.lowerBarQ t (a.advance t x d).1))
      (.ofRat (a.upperBarQ t (a.advance t x d).1)) =
        a.stateUpper (t + 1) (a.advance t x d) := by
  simp only [rescaledLower, rescaledUpper, stateLower, stateUpper, Fraction.value_ofRat,
    r.value (t + 1) (Nat.succ_pos t), Bool.false_eq_true, ite_false, ite_true,
    Coefficients.advance, Coefficients.thresholdsQ, and_self]

end

end SampLib.EnvelopeFactory.Coefficients.Realization
