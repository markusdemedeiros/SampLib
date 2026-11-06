import SampLib.General.StoppedSum
import SampLib.General.Laws.Episodes

/-! # A stopped sum together with its sampled episode length -/

open ProbLang
open scoped ENNReal

namespace SampLib.Episodes

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def encode (p : ℤ × ℕ) : Val rT := .pair (.int p.1) (.int (p.2 : ℤ))

theorem twp_episodes (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ × ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ p, F p ∂law ν μ) -∗
      tglWp E pl(&Occil.General.episodes &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ p : ℤ × ℕ, ⌜v = encode p⌝ ∗ ↯ (F p))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&counter.fst #())
  isimp only [← expectation ν μ F] at Hcredit
  iapply (hcounter.wp (fun n => ∫⁻ z, F (z, n) ∂StoppedSum.sumLaw μ n)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 4 twp_pure
  twp_bind pl(&(StoppedSum.sumLoop sample) #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (StoppedSum.twp_sumLoop E μ sample hsample n (fun z => F (z, n))) $$ Hcredit
  iintro %v ⟨%z, %hv, Hcredit⟩
  subst v
  twp_value
  imodintro
  iexists (z, n)
  iframe Hcredit
  ipureintro
  rfl

/-- Typed joint episode law, with arbitrary natural stopping distributions. -/
theorem episodes_distSpec (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int) :
    IsDistSpec (GF := GF) E pl(&Occil.General.episodes &counter.fst &sample.fst #())
      (law ν μ) encode where
  spec F _ := wand_entails (twp_episodes E ν μ counter sample hcounter hsample F)

end specification

end

end SampLib.Episodes
