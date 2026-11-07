import SampLib.PSRN.Support.Root.Bracket
import SampLib.PSRN.Support.Root.Bisection
import SampLib.PSRN.Syntax.PSRNRootStages

/-! # Observing a nonnegative deferred root without resampling its source

Two exact integer powers fix the rational grid. The expanding bracket and finite
bisection then return an enclosure of the same latent source value's root.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

private theorem Bracketed.of_upper {D : Model Ω S} {degree : ℕ} {denominator hi : ℤ} {s : S}
    (hdegree : degree ≠ 0) (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x)
    (hupper : ∀ᵐ x ∂D.posterior s, D.value x < ((hi : ℝ) / denominator) ^ degree) :
    Bracketed D degree denominator 0 hi s := by
  filter_upwards [hnonneg, hupper] with x hx hu
  simpa only [Int.cast_zero, zero_div, zero_pow hdegree] using And.intro hx hu

private theorem dyadic_width {I : RationalInterval} {n : ℕ}
    (h : I.width ≤ 1 / (((2 : ℤ) ^ n : ℤ) : ℝ)) : I.width ≤ (1 / 2 : ℝ) ^ n := by
  simpa only [Int.cast_pow, Int.cast_ofNat, one_div_pow] using h

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- One actual root read retains the source cache and returns a dyadic-width enclosure. -/
theorem twp_observe (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : 2 ≤ degree) (s : S) (hadmissible : Admissible D degree s)
    (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.value source degree).fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = intervalVal I ∧ D.refines s t ∧ (D.nthRoot degree).Encloses t n I ∧
            I.denominator = (2 : ℤ) ^ n ∧ I.upper = I.lower + 1 ∧
            (∀ᵐ x ∂D.posterior t, ⌊root degree (D.value x) * ((2 : ℤ) ^ n)⌋ = I.lower)⌝ ∗
          P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t))) := by
  have hd : 0 < (2 : ℤ) ^ n := by positivity
  have hdegree0 : degree ≠ 0 := by omega
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_begin E source degree n _
  iapply Program.twp_power_denominator E source degree n _
  iapply Program.twp_power_grid E source degree ((2 : ℤ) ^ n) _
  iapply Program.twp_bind_bracket E source degree ((2 : ℤ) ^ n) _
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_bracket E D hD P source hsource degree hdegree0 ((2 : ℤ) ^ n) hd s
      hadmissible F hF
    iframe Hstate Hcredit
  iintro %upper Hpost
  isimp only [bracketPost] at Hpost
  icases Hpost with ⟨%hi, %t, %ht, Hstate, Hcredit⟩
  rcases ht with ⟨rfl, hhi, hst, hupper⟩
  iapply Program.twp_open_bisect E source degree ((2 : ℤ) ^ n) hi _
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_bisect E D hD P source hsource degree hdegree0 ((2 : ℤ) ^ n) hd
      s t hst hadmissible 0 hi (by omega) (by omega)
      (Bracketed.of_upper hdegree0 (hadmissible.refines hst).1 hupper) F hF
    iframe Hstate Hcredit
  iintro %result Hpost
  isimp only [bisectPost] at Hpost
  icases Hpost with ⟨%u, %I, %hI, Hstate, Hcredit⟩
  rcases hI with ⟨rfl, hsu, hcontains, hwidth, hdenominator, hgap, hfloor⟩
  iexists u, I
  iframe Hstate Hcredit
  ipureintro
  exact ⟨rfl, hsu, hcontains.mono fun _ hx => ⟨hx, dyadic_width hwidth⟩,
    hdenominator, hgap, by simpa only [Int.cast_pow] using hfloor⟩

end specification

end

end SampLib.LatentReal.Root
