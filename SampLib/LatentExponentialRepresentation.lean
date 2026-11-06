import SampLib.LatentExponentialObservation
import SampLib.LatentRepresentedDigits
import SampLib.LatentRepresentedTranslate

/-! # The exponential's actual whole-plus-digits interval schedule -/

open MeasureTheory

namespace SampLib.LatentExponential

noncomputable section

open LatentReal ExponentialDigits

abbrev fractionModel (rate : ℝ) (hrate : 0 < rate) : Model ℝ (DigitState rate) :=
  @LatentDigits.model ℝ _ (fraction rate) (fraction_probability rate hrate)
    digits measurable_digits

def fractionRepresentation (rate : ℝ) (hrate : 0 < rate) :
    Representation (fractionModel rate hrate) :=
  @LatentDigits.representation ℝ _ (fraction rate) (fraction_probability rate hrate)
    digits measurable_digits

private theorem point_approximates (k : ℕ) :
    RationalInterval.Approximates (fun _ => RationalInterval.point (k : ℤ) 1 (by decide))
      (k : ℝ) := by
  refine ⟨fun _ => (RationalInterval.contains_point _ _ _ _).mpr (by simp), ?_⟩
  simp [RationalInterval.width, RationalInterval.lowerReal, RationalInterval.upperReal,
    RationalInterval.point]

/-- The whole is exact; all remaining uncertainty is the original fractional digit interval. -/
def representation (rate : ℝ) (hrate : 0 < rate) : Representation (model rate hrate) where
  interval n z := (RationalInterval.point (z.1 : ℤ) 1 (by decide)).add
    ((fractionRepresentation rate hrate).interval n z.2)
  measurable_lower n := by
    exact (((measurable_of_countable (fun k : ℕ => (k : ℤ))).comp measurable_fst).mul
      (((fractionRepresentation rate hrate).measurable_denominator n).comp measurable_snd)).add
        ((((fractionRepresentation rate hrate).measurable_lower n).comp measurable_snd).mul_const 1)
  measurable_upper n := by
    exact (((measurable_of_countable (fun k : ℕ => (k : ℤ))).comp measurable_fst).mul
      (((fractionRepresentation rate hrate).measurable_denominator n).comp measurable_snd)).add
        ((((fractionRepresentation rate hrate).measurable_upper n).comp measurable_snd).mul_const 1)
  measurable_denominator n :=
    measurable_const.mul
      (((fractionRepresentation rate hrate).measurable_denominator n).comp measurable_snd)
  approximates s := by
    have := fraction_probability rate hrate
    cases s with
    | none =>
      have hfraction := (fractionRepresentation rate hrate).approximates
        (LatentDigits.initial (fraction rate) digits)
      rw [LatentDigits.posterior_initial] at hfraction
      have hprod := (Measure.quasiMeasurePreserving_snd
        (μ := ProbabilityTheory.geometricMeasure (wholeBias rate hrate))
        (ν := fraction rate)).ae hfraction
      filter_upwards [hprod] with z hz
      exact (point_approximates z.1).add hz
    | some kp =>
      rcases kp with ⟨k, p⟩
      have hprod := (Measure.quasiMeasurePreserving_snd (μ := Measure.dirac k)
        (ν := DigitPosterior.law (fraction rate) digits p.val)).ae
          ((fractionRepresentation rate hrate).approximates p)
      filter_upwards [hprod] with z hz
      exact (point_approximates z.1).add hz

/-- A represented fractional read identifies the full interval once the whole is retained. -/
theorem observed_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p : DigitState rate)
    (n : ℕ) (I : RationalInterval)
    (hI : (Representation.translate (fractionModel rate hrate)
      (fractionRepresentation rate hrate) (k : ℤ) 1 (by decide)).Observed p n I) :
    (representation rate hrate).Observed (some (k, p)) n I := by
  have := fraction_probability rate hrate
  have hfraction := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hI
  have hk : ∀ᵐ j ∂Measure.dirac k, j = k := by simp [ae_dirac_eq]
  have hwhole := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hk
  filter_upwards [hfraction, hwhole] with z hz hk
  change I = (RationalInterval.point (z.1 : ℤ) 1 (by decide)).add
    ((fractionRepresentation rate hrate).interval n z.2)
  rw [hk]
  exact hz

end

end SampLib.LatentExponential
