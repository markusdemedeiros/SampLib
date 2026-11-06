import SampLib.Latent.LatentDigitAllocation
import SampLib.Latent.LatentDigitModel
import SampLib.Latent.LatentPayloadSpec

/-! # Constructor ownership for a conditional digit stream

This is only the constructor component. The full sampler law additionally needs
the next-digit kernel and a proof of every finite observation of this closure.
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

/-- The returned closure and its entire prefix cache share one physical root. -/
def owns (μ : Measure Ω) (digits : Ω → ℕ → Bool) (nextBit : Val rT)
    (v : Val rT) (p : State μ digits) : IProp GF :=
  iprop(∃ root : Loc, ⌜v = Syntax.oracleVal nextBit root⌝ ∗ UniformBag.owns root p.val)

/-- Construction reveals no digits and therefore leaves the whole prior credit intact. -/
theorem payloadSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) :
    LatentReal.IsLatentPayloadSpec (GF := GF) E
      pl(&Occil.PSRN.newByDigits &nextBit.fst #())
      (model μ digits hd) (initial μ digits) (owns μ digits nextBit) where
  spec F _ := by
    iintro Hcredit
    isimp only [posterior_initial] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply twp_allocate E nextBit _ $$ Hcredit
    iintro %v ⟨%root, %hv, Hroot, Hcredit⟩
    iexists initial μ digits
    isplit
    · ipureintro
      exact List.prefix_refl _
    isplitl [Hroot]
    · isimp only [owns, initial]
      iexists root
      iframe Hroot
      ipureintro
      exact hv
    isimp only [posterior_initial]
    iexact Hcredit

end

end SampLib.LatentDigits
