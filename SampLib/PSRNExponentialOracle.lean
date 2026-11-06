import SampLib.PSRNExponentialDecay
import SampLib.LatentExponentialRepresentation

/-! # Observing one decay-based exponential

The sampled whole part stays fixed. Every query reads the same fractional cache,
and its credit retains both coordinates of the original joint world.
-/

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
