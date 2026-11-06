import SampLib.Latent.LatentDigitRead
import SampLib.Latent.LatentDigitConstructor

/-! # Conditional digit samplers with an owned shared latent law

The callback supplies each next digit's conditional law. Construction defers all
digits, and every observation preserves the same physical cache and whole-world
posterior, including shorter rereads and repeated aliases of the returned closure.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentDigits

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A query exposes the requested prefix while retaining the complete cache and posterior. -/
theorem twp_observe (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (v : Val rT) (p : State μ digits) (n : ℕ) (F : Ω → ℝ≥0∞) :
    iprop(owns μ digits nextBit v p ∗ ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits p.val)) ⊢
      tglWp E pl(&v.fst #int (n : ℤ)) (fun result : Val rT => iprop(∃ q : State μ digits,
        ⌜UniformBag.readRefines p.val n q.val ∧
          result = LatentReal.intervalVal (LatentUniform.interval q.val n)⌝ ∗
        owns μ digits nextBit v q ∗ ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits q.val))) := by
  iintro ⟨Hstate, Hcredit⟩
  isimp only [owns] at Hstate
  icases Hstate with ⟨%root, %hv, Hroot⟩
  subst v
  iapply Syntax.twp_oracle_apply
  iapply tglWp_wand
  isplitl [Hroot Hcredit]
  · have hread := twp_read (rT := rT) (GF := GF) E μ digits hd nextBit hnext root [] p.val n
      (by simpa only [List.nil_append] using p.property) F
    simp only [UniformBag.rank, List.length_nil, pow_zero] at hread
    iapply hread
    isimp only [List.nil_append]
    iframe Hroot Hcredit
  iintro %result Hpost
  isimp only [readPost] at Hpost
  icases Hpost with ⟨%q, %hq, Hroot, Hcredit⟩
  rcases hq with ⟨hread, hp, hresult⟩
  let state : State μ digits := ⟨q, by simpa only [List.nil_append] using hp⟩
  iexists state
  isplit
  · ipureintro
    exact ⟨hread, by simpa only [readInterval_nil] using hresult⟩
  isplitl [Hroot]
  · isimp only [owns]
    iexists root
    iframe Hroot
    itrivial
  isimp only [List.nil_append] at Hcredit
  iexact Hcredit

/-- All finite observations use one joint law, including nonuniform and dependent digits. -/
theorem oracleSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit) :
    LatentReal.IsOracleSpec (GF := GF) E (model μ digits hd) (owns μ digits nextBit) where
  observe v p n F _ := by
    iintro Hstate
    isimp only [model] at Hstate
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_observe E μ digits hd nextBit hnext v p n F $$ Hstate
    iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
    rcases hq with ⟨hread, rfl⟩
    iexists q, LatentUniform.interval q.val n
    rw [show (model μ digits hd).posterior q = DigitPosterior.law μ digits q.val from rfl]
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, hread.1, interval_encloses μ digits hd hread⟩

/-- The original memoized constructor implements the specified full latent digit law. -/
theorem newByDigits_latentDistSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newByDigits &nextBit.fst #())
      (model μ digits hd) (initial μ digits) (owns μ digits nextBit) where
  oracle := oracleSpec E μ digits hd nextBit hnext
  spec := (payloadSpec E μ digits hd nextBit).spec

end

end SampLib.LatentDigits
