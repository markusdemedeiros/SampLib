import SampLib.Latent.LatentDigitModel
import SampLib.Latent.Laws.DigitKernel
import SampLib.Core.SupportedSpec

/-! # Conditional callbacks for the memoized digit sampler

The callback is specified at the current prefix's conditional next-bit law.
Applying it exchanges joint posterior credit for a reachable child posterior;
this remains valid for dependent digits and zero-probability branches.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentDigits

noncomputable section

section mathematics

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω]

private theorem next_support (μ : Measure Ω)
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) :
    ∀ᵐ b ∂DigitPosterior.nextLaw μ digits p,
      μ (DigitPosterior.cylinder digits (p ++ [b])) ≠ 0 :=
  ae_iff_of_countable.mpr fun b hb => DigitPosterior.next_supported μ hd p b hb

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A fresh callback call uses the conditional law determined by its prefix arguments. -/
structure IsNextDigitSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) : Prop where
  coin (p : State μ digits) :
    let := DigitPosterior.nextLaw_probability μ hd p.val p.property
    IsDistSpec (GF := GF) E
      pl(&nextBit.fst #int (UniformBag.rank p.val) #int (2 ^ p.val.length))
      (DigitPosterior.nextLaw μ digits p.val) Val.bool

/-- A fresh digit retains credit on the entire underlying world, rather than just its bit. -/
theorem IsNextDigitSpec.wp {E : CoPset} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {digits : Ω → ℕ → Bool} {hd : ∀ n, Measurable (fun x => digits x n)}
    {nextBit : Val rT} (h : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (p : State μ digits) (F : Ω → ℝ≥0∞) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits p.val) -∗
      (∀ b : Bool, ⌜μ (DigitPosterior.cylinder digits (p.val ++ [b])) ≠ 0⌝ -∗
        ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits (p.val ++ [b])) -∗ Φ (Val.bool b)) -∗
      tglWp E pl(&nextBit.fst #int (UniformBag.rank p.val) #int (2 ^ p.val.length)) Φ := by
  let := DigitPosterior.nextLaw_probability μ hd p.val p.property
  iintro Hcredit Hcont
  isimp only [← DigitPosterior.next_expectation μ hd p.val F] at Hcredit
  iapply ((h.coin p).wp_supported
    (fun b => μ (DigitPosterior.cylinder digits (p.val ++ [b])) ≠ 0)
    ((Set.toFinite _).measurableSet) (next_support μ hd p.val)
    (fun b => ∫⁻ x, F x ∂DigitPosterior.law μ digits (p.val ++ [b]))
    (measurable_of_finite _) Φ) $$ Hcredit
  iintro %b %hb Hcredit
  iapply Hcont $$ %b %hb Hcredit

end specification

end

end SampLib.LatentDigits
