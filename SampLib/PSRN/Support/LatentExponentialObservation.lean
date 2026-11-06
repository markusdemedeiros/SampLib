import SampLib.PSRN.Support.LatentExponentialModel
import SampLib.PSRN.Support.LatentRationalTranslate

/-! # Observing an exponential's fixed whole and deferred fraction

Translation observes the same fractional posterior. Adding the fixed whole
coordinate to that world preserves both its enclosure and its dyadic error.
-/

open MeasureTheory

namespace SampLib.LatentExponential

noncomputable section

open ExponentialDigits

/-- Once the integer is fixed, refinement is exactly extension of the fractional prefix. -/
theorem refines_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p q : DigitState rate) :
    (model rate hrate).refines (some (k, p)) (some (k, q)) ↔ p.val <+: q.val := by
  change (k = k ∧ p.val <+: q.val) ↔ p.val <+: q.val
  simp

/-- A translated fractional enclosure is an enclosure of the same exponential world. -/
theorem encloses_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p : DigitState rate)
    (n : ℕ) (I : LatentReal.RationalInterval)
    (hI : ((@LatentDigits.model ℝ _ (fraction rate) (fraction_probability rate hrate)
      digits measurable_digits).translate (k : ℝ)).Encloses p n I) :
    (model rate hrate).Encloses (some (k, p)) n I := by
  let := fraction_probability rate hrate
  let := DigitPosterior.probability (fraction rate) digits p.val p.property
  change ∀ᵐ x ∂DigitPosterior.law (fraction rate) digits p.val,
    I.Contains ((k : ℝ) + DigitPosterior.value (digits x)) ∧
      I.upperReal - I.lowerReal ≤ (2 ^ n : ℝ)⁻¹ at hI
  change ∀ᵐ z ∂(Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val),
    I.Contains ((z.1 : ℝ) + DigitPosterior.value (digits z.2)) ∧
      I.upperReal - I.lowerReal ≤ (2 ^ n : ℝ)⁻¹
  have hfraction := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hI
  have hk : ∀ᵐ j ∂Measure.dirac k, j = k := by simp [ae_dirac_eq]
  have hwhole : ∀ᵐ z ∂(Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val),
      z.1 = k := (Measure.quasiMeasurePreserving_fst
        (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hk
  filter_upwards [hfraction, hwhole] with z hz hk
  simpa only [hk] using hz

end

end SampLib.LatentExponential
