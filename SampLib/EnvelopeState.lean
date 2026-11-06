import SampLib.EnvelopePosterior

/-! # Canonical rational state passed to the actual envelope loop -/

namespace SampLib.EnvelopeFactory.Coefficients

open FactoryFractions

noncomputable section

abbrev stateLower (a : Coefficients) (t : ℕ) (x : a.State t) : Fraction :=
  .ofRat (a.thresholdsQ t x.1 x.2).1

abbrev stateUpper (a : Coefficients) (t : ℕ) (x : a.State t) : Fraction :=
  .ofRat (a.thresholdsQ t x.1 x.2).2

theorem stateLower_coe (a : Coefficients) (p : unitInterval) (t : ℕ) (x : a.State t) :
    ((a.stateLower t x).value : ℝ) = (a.process p).lower t x := by
  simpa only [stateLower, Fraction.value_ofRat, process] using (a.thresholdsQ_coe t x.1 x.2).1

theorem stateUpper_coe (a : Coefficients) (p : unitInterval) (t : ℕ) (x : a.State t) :
    ((a.stateUpper t x).value : ℝ) = (a.process p).upper t x := by
  simpa only [stateUpper, Fraction.value_ofRat, process] using (a.thresholdsQ_coe t x.1 x.2).2

end

end SampLib.EnvelopeFactory.Coefficients
