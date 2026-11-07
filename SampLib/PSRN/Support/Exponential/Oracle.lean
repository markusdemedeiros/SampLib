import SampLib.PSRN.Support.Exponential.Model
import SampLib.PSRN.Support.Represented.Digits
import SampLib.PSRN.Support.Represented.Translate
import SampLib.PSRN.Support.Exponential.Decay

/-! # Observing one decay-based exponential

The sampled whole part stays fixed. Every query reads the same fractional cache,
and its credit retains both coordinates of the original joint world.
-/

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

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNExponential

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The fractional closure owns its actual memoized digit root. -/
abbrev fractionOwns (rate : ℝ) (decay : Val rT) (v : Val rT)
    (p : LatentExponential.DigitState rate) : IProp GF :=
  LatentDigits.owns (ExponentialDigits.fraction rate) ExponentialDigits.digits
    (ExponentialLogistic.Program.digitVal decay) v p

/-- Observation retains the translated fractional closure and its fixed whole part. -/
def owns (rate : ℝ) (decay : Val rT) (v : Val rT) : LatentExponential.State rate → IProp GF
  | none => iprop(⌜False⌝)
  | some (k, p) => LatentReal.translateOwns (fractionOwns rate decay) (k : ℤ) 1 v p

/-- Actual translated observations preserve the complete whole/fraction posterior. -/
theorem representedOracleSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT)
    (hdecay : IsDecaySpec (GF := GF) E rate hrate decay) :
    LatentReal.IsRepresentedOracleSpec (GF := GF) E (LatentExponential.model rate hrate)
      (LatentExponential.representation rate hrate) (owns rate decay) where
  observe v s n F hF := by
    have := ExponentialDigits.fraction_probability rate hrate
    cases s with
    | none =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [owns] at Hstate
      ihave %hfalse := Hstate
      exact False.elim hfalse
    | some kp =>
      rcases kp with ⟨k, p⟩
      have hG : Measurable (fun x : ℝ => F (k, x)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      have hfrac := LatentDigits.representedOracleSpec (rT := rT) (GF := GF) E
        (ExponentialDigits.fraction rate) ExponentialDigits.digits
        ExponentialDigits.measurable_digits (ExponentialLogistic.Program.digitVal decay)
        (digitSpec E rate hrate decay hdecay)
      have htranslated := LatentReal.represented_translate_oracleSpec E
        (LatentDigits.model (ExponentialDigits.fraction rate) ExponentialDigits.digits
          ExponentialDigits.measurable_digits) (LatentExponential.fractionRepresentation rate hrate)
        (fractionOwns rate decay) hfrac
        (k : ℤ) 1 (by decide)
      have hread := htranslated.observe v p n (fun x => F (k, x)) hG
      iintro ⟨Hstate, Hcredit⟩
      isimp only [owns] at Hstate
      isimp only [LatentExponential.some_expectation rate hrate k p F hF] at Hcredit
      iapply tglWp_wand
      isplitl [Hstate Hcredit]
      · iapply hread
        isimp only [LatentReal.Model.translate, LatentDigits.model]
        iframe Hstate Hcredit
      iintro %result ⟨%q, %I, %hI, Hstate, Hcredit⟩
      rcases hI with ⟨rfl, hrefines, hencloses, hobserved⟩
      isimp only [LatentReal.Model.translate, LatentDigits.model] at Hcredit
      iexists some (k, q), I
      isimp only [owns, LatentExponential.some_expectation rate hrate k q F hF]
      iframe Hstate Hcredit
      ipureintro
      refine ⟨trivial, (LatentExponential.refines_some rate hrate k p q).mpr hrefines, ?_, ?_⟩
      · apply LatentExponential.encloses_some rate hrate k q n I
        simpa only [Int.cast_natCast, Int.cast_one, div_one] using hencloses
      · exact LatentExponential.observed_some rate hrate k q n I hobserved

/-- Forget only the deterministic interval certificate; all owned joint credit remains. -/
theorem oracleSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT)
    (hdecay : IsDecaySpec (GF := GF) E rate hrate decay) :
    LatentReal.IsOracleSpec (GF := GF) E (LatentExponential.model rate hrate)
      (owns rate decay) :=
  (representedOracleSpec E rate hrate decay hdecay).forget

end

end SampLib.PSRNExponential
