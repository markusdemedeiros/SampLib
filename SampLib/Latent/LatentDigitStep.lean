import SampLib.Latent.LatentDigitKernel
import SampLib.Latent.Syntax.PSRNDigits

/-! # One step of the original conditional digit reader

Cached digits are returned without resampling. A fresh digit uses the conditional
callback exactly once, then stores that bit and the newly allocated tail.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentDigits

open scoped Syntax

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The fresh branch samples the next conditional digit and retains both owned cells. -/
theorem twp_fresh (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (root : Loc) (p : State μ digits) (F : Ω → ℝ≥0∞) :
    iprop(UniformBag.owns root [] ∗ ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits p.val)) ⊢
      tglWp E (Syntax.fresh nextBit root (UniformBag.rank p.val) (2 ^ p.val.length))
        (fun v : Val rT => iprop(∃ (b : Bool) (tail : Loc),
          ⌜v = Val.pair (Val.bool b) (Val.loc tail) ∧
            μ (DigitPosterior.cylinder digits (p.val ++ [b])) ≠ 0⌝ ∗
          appHeapFrag root (UniformBag.nodeVal b tail) ∗ UniformBag.owns tail [] ∗
          ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits (p.val ++ [b])))) := by
  iintro ⟨Hroot, Hcredit⟩
  isimp only [UniformBag.owns] at Hroot
  unfold Syntax.fresh
  twp_pures
  twp_bind (Exp.alloc (Exp.ofVal (UniformBag.emptyVal : Val rT)))
  iapply twp_alloc
  iintro %tail Htail
  twp_pure
  isimp only [Syntax.bind, Exp.openRec, Syntax.open_value]
  twp_bind pl(&nextBit.fst #int (UniformBag.rank p.val) #int (2 ^ p.val.length))
  iapply (hnext.wp p F _) $$ Hcredit
  iintro %b %hb Hcredit
  twp_pures
  twp_bind (Exp.store pl(#loc root) (Exp.ofVal (UniformBag.nodeVal b tail)))
  iapply twp_store
  iframe Hroot
  iintro Hroot
  twp_pures
  twp_value
  imodintro
  iexists b, tail
  isimp only [UniformBag.owns]
  iframe Hroot Htail Hcredit
  ipureintro
  exact ⟨trivial, hb⟩

end

end SampLib.LatentDigits
